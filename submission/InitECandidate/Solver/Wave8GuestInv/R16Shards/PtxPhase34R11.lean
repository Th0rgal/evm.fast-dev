import InitECandidate.Solver.Wave8GuestInv.R16Shards.PtxPhase1R11
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.AccountWk
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBalStateInit.SetLstNew
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.EncodeReceipt

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R13Shards

/-- Before the Phase-4 stable copy, the header and live pointer array may be
scratch-resident. `frame_new` uses `lst_new_scratch`; `lst_push` moves only the
backing array to the heap when it grows. -/
def LogsLiveOwned {F : Type} (s : PanSemStateFiniteExact 64 F)
    (S Nd : List Nat) (logs : Nat) : Prop :=
  logs ≠ 0 →
    Allocated s (memW s logs, 8 * memW s (logs + 8)) ∧
    IvlsDisj [(logs, 24), (memW s logs, 8 * memW s (logs + 8))] (worldOwned s S Nd) ∧
    ∀ i, i < memW s (logs + 8) →
      IvlsDisj (logOwnedIvls s (memW s (memW s logs + 8 * i))) (worldOwned s S Nd)

/-- The message result owns its live log storage outside the world, without
requiring the temporary header or its initial array to be heap-resident. -/
def RetMessageOutputStrong : ∀ {F : Type}, PanSemStateFiniteExact 64 F →
    Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop :=
  fun s r post S Nd => RetMessageOutput s r post S Nd ∧
    ∀ v, r = some (.returned v) → ∃ w : BitVec 64,
      v = .val (.word w) ∧ LogsLiveOwned post S Nd (memW post (w.toNat + 16))

def TxAfterCallStrong : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => TxWorld s ∧ WordsOK s (locN s "out", 96) ∧
    Inside (locN s "out", 96) sourceBase (globN s "heap_ptr") ∧
    LogsListOK s (memW s (locN s "out" + 16)) ∧
    ∃ S Nd, WorldTypedWith s S Nd ∧
      IvlsDisj [(locN s "out", 96)] (worldOwned s S Nd) ∧
      LogsLiveOwned s S Nd (memW s (locN s "out" + 16))

def BoListArgStrong : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => WorldOK s ∧ BoListArg s ∧ memW s (locN s "l") ≠ 0

/-- The two block-output lists have non-null backing pointers.
This concerns the word in each list header, rather than just the header
pointer stored in the block-output record. -/
def TxBacking : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => memW s (memW s (globN s "bo" + 40)) ≠ 0 ∧
    memW s (memW s (globN s "bo" + 72)) ≠ 0

/-- Local cutover guard; the frozen transaction contract remains a projection. -/
def TxReadyBackingStrong : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => TxReadyStrong s ∧ TxBacking s

/-- Intermediate environment carrying both backing-pointer facts. -/
def TxEnvBackingStrong : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => TxEnv s ∧ TxBacking s

def TxAfterCallBackingStrong : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => TxAfterCallStrong s ∧ TxBacking s

theorem txBacking_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    TxBacking {s with locals := locals, clock := k} ↔ TxBacking s := Iff.rfl

theorem txBacking_set_local {F : Type} {s : PanSemStateFiniteExact 64 F}
    (name : MlS) (v : ValueHOL 64) (h : TxBacking s) :
    TxBacking (setVarHOLFinite name v s) := h

theorem txReadyBackingStrong_env {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : TxReadyBackingStrong s) : TxEnvBackingStrong s :=
  ⟨PtxP1.txEnv_of_ready h.1, h.2⟩

theorem txReadyBackingStrong_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat)
    (ht : locals.lookup (ofString "tx") = s.locals.lookup (ofString "tx"))
    (hi : locals.lookup (ofString "index") = s.locals.lookup (ofString "index"))
    (h : TxReadyBackingStrong s) :
    TxReadyBackingStrong {s with locals := locals, clock := k} :=
  ⟨PtxP1.txReadyStrong_with_locals s locals k ht hi h.1, h.2⟩

theorem txEnvBackingStrong_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat)
    (hi : locals.lookup (ofString "index") = s.locals.lookup (ofString "index"))
    (h : TxEnvBackingStrong s) :
    TxEnvBackingStrong {s with locals := locals, clock := k} :=
  ⟨R13Shards.txEnv_with_locals s locals k hi h.1, h.2⟩

/-- Transport needs the nested header words as well as the outer record words.
Keeping only `bo+40` and `bo+72` does not supply the second premise. -/
theorem txBacking_of_header_words {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (h : TxBacking s) (hbo : globN post "bo" = globN s "bo")
    (hheaders : ∀ k ∈ ([40, 72] : List Nat),
      memW post (globN s "bo" + k) = memW s (globN s "bo" + k))
    (hbacking : ∀ k ∈ ([40, 72] : List Nat),
      memW post (memW s (globN s "bo" + k)) = memW s (memW s (globN s "bo" + k))) :
    TxBacking post := by
  constructor
  · rw [hbo, hheaders 40 (by simp), hbacking 40 (by simp)]
    exact h.1
  · rw [hbo, hheaders 72 (by simp), hbacking 72 (by simp)]
    exact h.2

/-- A single store outside both block-output slots and both list-header data
words preserves backing, regardless of the stored value. -/
theorem txBacking_store {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : TxBacking s) {x : BitVec 64} {mem' : BitVec 64 → HolWordLab 64}
    (hm : ∀ a, a ≠ x → mem' a = s.memory a)
    (hslots : ∀ k ∈ ([40, 72] : List Nat), BitVec.ofNat 64 (globN s "bo" + k) ≠ x)
    (hheaders : ∀ k ∈ ([40, 72] : List Nat),
      BitVec.ofNat 64 (memW s (globN s "bo" + k)) ≠ x) :
    TxBacking {s with memory := mem'} := by
  apply txBacking_of_header_words (post := {s with memory := mem'}) h rfl
  · intro k hk
    unfold memW
    dsimp only
    rw [hm _ (hslots k hk)]
  · intro k hk
    unfold memW at hheaders ⊢
    dsimp only
    rw [hm _ (hheaders k hk)]

/-- Caller locals read by Phase 4 before they are assigned there. `out` is
introduced by Phase 3 itself. The message-building locals `mgas`, `reservoir`
and `m` are not read by Phase 4. -/
def PtxPhase4LocalShapes : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s =>
    (∀ name ∈ (["tx", "index", "sender", "gas", "tx_blob_gas_used"] : List String),
      ∃ w : BitVec 64, s.locals.lookup (ofString name) = some (.val (.word w))) ∧
    (∃ v, s.locals.lookup (ofString "price") = some v ∧
      shapeOfHOLExact v = .comb [.one, .one, .one, .one]) ∧
    (∃ v, s.locals.lookup (ofString "intrinsic") = some v ∧
      shapeOfHOLExact v = .comb [.one, .one, .one])

theorem ptxPhase4LocalShapes_resume {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (h : PtxPhase4LocalShapes s) :
    PtxPhase4LocalShapes (setVarHOLFinite (ofString "out") v { post with locals := s.locals }) := by
  have hlu : ∀ name : String, ofString name ≠ ofString "out" →
      (setVarHOLFinite (ofString "out") v { post with locals := s.locals }).locals.lookup
        (ofString name) = s.locals.lookup (ofString name) := by
    intro name hn
    simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, Ne.symm hn]
  refine ⟨?_, ?_, ?_⟩
  · intro name hn
    have hne : ofString name ≠ ofString "out" := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl | rfl | rfl | rfl <;> decide
    rw [hlu name hne]
    exact h.1 name hn
  · rw [hlu "price" (by decide)]; exact h.2.1
  · rw [hlu "intrinsic" (by decide)]; exact h.2.2

namespace PtxP34
open PtxP1

/-- Lift a concrete word store to the backing invariant. The destination
separation obligations are stated on evaluated addresses, so callers can use
the existing spatial store proofs without unfolding the store semantics. -/
theorem hoare_store_backing
    (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (dst src : ExpHOL 64)
    (hword : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
      P s → evalAt s src = some v → ∃ w : HolWordLab 64, v = .val w)
    (hsep : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (x : BitVec 64),
      P s → evalAt s dst = some (.val (.word x)) →
      ∀ k ∈ ([40, 72] : List Nat),
        BitVec.ofNat 64 (globN s "bo" + k) ≠ x ∧
        BitVec.ofNat 64 (memW s (globN s "bo" + k)) ≠ x) :
    Hoare (fun s => P s ∧ TxBacking s) (.store dst src)
      (fun r post => r = none → TxBacking post) := by
  apply R13Shards.Hoare.store_fall
  intro F s x v mem' hp hx hv hm
  obtain ⟨w, rfl⟩ := hword s v hp.1 hv
  obtain ⟨_, _, hframe⟩ := R13Shards.panMemStoresHOL_word_spec
    (by simpa only [flattenHOL] using hm)
  exact txBacking_store hp.2 hframe
    (fun k hk => (hsep s x hp.1 hx k hk).1)
    (fun k hk => (hsep s x hp.1 hx k hk).2)

/-- Spatial form of backing transport: preserving the block-output record and
the two list headers preserves both levels of pointer lookup. -/
theorem txBacking_of_unhit_headers {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (h : TxBacking s) (hbo : globN post "bo" = globN s "bo")
    (hbo8 : globN s "bo" % 8 = 0)
    (hbob : globN s "bo" + 88 ≤ 2 ^ 64)
    (hbu : IvlUnhit s post (globN s "bo", 88))
    (hl8 : ∀ k ∈ ([40, 72] : List Nat), memW s (globN s "bo" + k) % 8 = 0)
    (hlb : ∀ k ∈ ([40, 72] : List Nat), memW s (globN s "bo" + k) + 24 ≤ 2 ^ 64)
    (hlu : ∀ k ∈ ([40, 72] : List Nat),
      IvlUnhit s post (memW s (globN s "bo" + k), 24)) :
    TxBacking post := by
  apply txBacking_of_header_words h hbo
  · intro k hk
    have hk' : k = 40 ∨ k = 72 := by simpa using hk
    apply memW_eq_of_ivlUnhit hbu
    · rcases hk' with rfl | rfl <;> omega
    · exact hbob
    · rcases hk' with rfl | rfl <;> dsimp only <;> omega
  · intro k hk
    exact memW_eq_of_ivlUnhit (hlu k hk) (hl8 k hk) (hlb k hk)
      ⟨le_rfl, by omega⟩

/-- The no-growth push writes only the length word at `l+8`. Its data word at
`l` is unchanged, with no assumption about the returned slot. -/
theorem backing_nonzero_of_length_store {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {l : Nat}
    (hn : memW s l ≠ 0) (hb : l + 24 ≤ 2 ^ 64)
    (hm : ∀ a : BitVec 64, ¬ CellHits a.toNat (l + 8, 8) →
      post.memory a = s.memory a) :
    memW post l ≠ 0 := by
  have he : memW post l = memW s l := by
    have hl : l < 2 ^ 64 := by omega
    have he := hm (BitVec.ofNat 64 l) (by
      unfold CellHits
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl]
      dsimp only
      omega)
    unfold memW
    rw [he]
  rwa [he]

/-- Concrete growth write: storing the allocator's nonzero result into the
list data word establishes nonzero backing. The header address is fixed across
the store; no return-slot contract is used. -/
theorem hoare_store_grown_backing (l : BitVec 64) :
    Hoare (fun s =>
      s.locals.lookup (ofString "l") = some (.val (.word l)) ∧
      ∃ np : BitVec 64, s.locals.lookup (ofString "np") = some (.val (.word np)) ∧
        np.toNat ≠ 0)
      (.store (.var .local (ofString "l")) (.var .local (ofString "np")))
      (fun r post => r = none → memW post l.toNat ≠ 0) := by
  apply R13Shards.Hoare.store_fall
  intro F s x v mem' hp hx hv hm
  obtain ⟨hl, np, hnp, hn⟩ := hp
  have hx' : x = l := by
    change s.locals.lookup (ofString "l") = some (.val (.word x)) at hx
    rw [hl] at hx
    cases hx
    rfl
  subst x
  have hv' : v = .val (.word np) := by
    change s.locals.lookup (ofString "np") = some v at hv
    rw [hnp] at hv
    exact (Option.some.inj hv).symm
  subst v
  obtain ⟨_, hwrite, _⟩ := R13Shards.panMemStoresHOL_word_spec
    (by simpa only [flattenHOL] using hm)
  change (match mem' (BitVec.ofNat 64 l.toNat) with | .word w => w.toNat) ≠ 0
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, hwrite]
  exact hn

/-- The actual growth-branch data write establishes nonzero backing from the
allocator result in `np`. -/
theorem hoare_lst_push_data_write (l : BitVec 64) :
    Hoare (fun s =>
      s.locals.lookup (ofString "l") = some (.val (.word l)) ∧
      ∃ np : BitVec 64, s.locals.lookup (ofString "np") = some (.val (.word np)) ∧
        np.toNat ≠ 0)
      (.store (.op .add [.var .local (ofString "l"), .const 0])
        (.var .local (ofString "np")))
      (fun r post => r = none → memW post l.toNat ≠ 0) := by
  apply R13Shards.Hoare.store_fall
  intro F s x v mem' hp hx hv hm
  obtain ⟨hl, np, hnp, hn⟩ := hp
  have hd : evalAt s (.op .add [.var .local (ofString "l"), .const 0]) =
      some (.val (.word l)) := by
    simp [evalAt, evalHOLExact, evalListHOLExact, hl, valueIsWord, valueWord,
      wordOpHOL, wordOp]
  rw [hd] at hx
  have he : x = l := by cases hx; rfl
  subst x
  have he : v = .val (.word np) := by
    change s.locals.lookup (ofString "np") = some v at hv
    rw [hnp] at hv
    exact (Option.some.inj hv).symm
  subst v
  obtain ⟨_, hwrite, _⟩ := R13Shards.panMemStoresHOL_word_spec
    (by simpa only [flattenHOL] using hm)
  change (match mem' (BitVec.ofNat 64 l.toNat) with | .word w => w.toNat) ≠ 0
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, hwrite]
  exact hn

/-- A length-only word store preserves the data word. -/
theorem hoare_store_list_length (l : BitVec 64) (src : ExpHOL 64)
    (hword : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
      evalAt s src = some v → ∃ w : HolWordLab 64, v = .val w) :
    Hoare (fun s => memW s l.toNat ≠ 0)
      (.store (.const (l + 8)) src)
      (fun r post => r = none → memW post l.toNat ≠ 0) := by
  apply R13Shards.Hoare.store_fall
  intro F s x v mem' hp hx hv hm
  have hx' : x = l + 8 := by
    change some (ValueHOL.val (.word (l + 8))) = some (ValueHOL.val (.word x)) at hx
    cases hx
    rfl
  subst x
  obtain ⟨w, rfl⟩ := hword s v hv
  obtain ⟨_, _, hframe⟩ := R13Shards.panMemStoresHOL_word_spec
    (by simpa only [flattenHOL] using hm)
  have hne : l ≠ l + 8 := by
    intro he
    have he' : (0 : BitVec 64) = 8 := by
      apply add_left_cancel (a := l)
      simpa using he
    exact (by decide : (0 : BitVec 64) ≠ 8) he'
  change (match mem' (BitVec.ofNat 64 l.toNat) with | .word w => w.toNat) ≠ 0
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, hframe l hne]
  simpa only [memW, BitVec.ofNat_toNat, BitVec.setWidth_eq] using hp

/-- The actual `lst_push` length-write expression preserves nonzero backing,
including modular evaluation of the address and increment. -/
theorem hoare_lst_push_length_write (l n : BitVec 64) :
    Hoare (fun s =>
      s.locals.lookup (ofString "l") = some (.val (.word l)) ∧
      s.locals.lookup (ofString "n") = some (.val (.word n)) ∧
      memW s l.toNat ≠ 0)
      (.store (.op .add [.var .local (ofString "l"), .const 8])
        (.op .add [.var .local (ofString "n"), .const 1]))
      (fun r post => r = none → memW post l.toNat ≠ 0) := by
  apply R13Shards.Hoare.store_fall
  intro F s x v mem' hp hx hv hm
  obtain ⟨hl, hn, hb⟩ := hp
  have hd : evalAt s (.op .add [.var .local (ofString "l"), .const 8]) =
      some (.val (.word (l + 8))) := by
    simp [evalAt, evalHOLExact, evalListHOLExact, hl, valueIsWord, valueWord,
      wordOpHOL, wordOp]
  have hs : evalAt s (.op .add [.var .local (ofString "n"), .const 1]) =
      some (.val (.word (n + 1))) := by
    simp [evalAt, evalHOLExact, evalListHOLExact, hn, valueIsWord, valueWord,
      wordOpHOL, wordOp]
  rw [hd] at hx
  have he : x = l + 8 := by cases hx; rfl
  subst x
  rw [hs] at hv
  have he : v = .val (.word (n + 1)) := (Option.some.inj hv).symm
  subst v
  obtain ⟨_, _, hframe⟩ := R13Shards.panMemStoresHOL_word_spec
    (by simpa only [flattenHOL] using hm)
  have hne : l ≠ l + 8 := by
    intro he
    have he' : (0 : BitVec 64) = 8 := by
      apply add_left_cancel (a := l)
      simpa using he
    exact (by decide : (0 : BitVec 64) ≠ 8) he'
  change (match mem' (BitVec.ofNat 64 l.toNat) with | .word w => w.toNat) ≠ 0
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, hframe l hne]
  simpa only [memW, BitVec.ofNat_toNat, BitVec.setWidth_eq] using hb

/-- The growth branch's capacity update preserves its newly installed backing
word, including modular multiplication of the capacity. -/
theorem hoare_lst_push_capacity_write (l cap : BitVec 64) :
    Hoare (fun s =>
      s.locals.lookup (ofString "l") = some (.val (.word l)) ∧
      s.locals.lookup (ofString "cap") = some (.val (.word cap)) ∧
      memW s l.toNat ≠ 0)
      (.store (.op .add [.var .local (ofString "l"), .const 16])
        (.panop .mul [.var .local (ofString "cap"), .const 2]))
      (fun r post => r = none → memW post l.toNat ≠ 0) := by
  apply R13Shards.Hoare.store_fall
  intro F s x v mem' hp hx hv hm
  obtain ⟨hl, hn, hb⟩ := hp
  have hd : evalAt s (.op .add [.var .local (ofString "l"), .const 16]) =
      some (.val (.word (l + 16))) := by
    simp [evalAt, evalHOLExact, evalListHOLExact, hl, valueIsWord, valueWord,
      wordOpHOL, wordOp]
  have hs : evalAt s (.panop .mul [.var .local (ofString "cap"), .const 2]) =
      some (.val (.word (cap * 2))) := by
    simp [evalAt, evalHOLExact, evalListHOLExact, hn, valueIsWord, valueWord,
      panOpHOL]
  rw [hd] at hx
  have he : x = l + 16 := by cases hx; rfl
  subst x
  rw [hs] at hv
  have he : v = .val (.word (cap * 2)) := (Option.some.inj hv).symm
  subst v
  obtain ⟨_, _, hframe⟩ := R13Shards.panMemStoresHOL_word_spec
    (by simpa only [flattenHOL] using hm)
  have hne : l ≠ l + 16 := by
    intro he
    have he' : (0 : BitVec 64) = 16 := by
      apply add_left_cancel (a := l)
      simpa using he
    exact (by decide : (0 : BitVec 64) ≠ 16) he'
  change (match mem' (BitVec.ofNat 64 l.toNat) with | .word w => w.toNat) ≠ 0
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, hframe l hne]
  simpa only [memW, BitVec.ofNat_toNat, BitVec.setWidth_eq] using hb

/-- The tail after either branch keeps nonzero backing through its return. -/
theorem lst_push_tail_backing_nonzero {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (l n : BitVec 64) (v : ValueHOL 64)
    (hc : s.code = originalRuntimeCode)
    (hl : s.locals.lookup (ofString "l") = some (.val (.word l)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (hb : memW s l.toNat ≠ 0)
    (hr : evaluateHOLFiniteState s
      (.seq (.store (.op .add [.var .local (ofString "l"), .const 8])
        (.op .add [.var .local (ofString "n"), .const 1]))
        (.return (.op .add
          [.load .one (.op .add [.var .local (ofString "l"), .const 0]),
           .panop .mul [.var .local (ofString "n"), .var .local (ofString "esz")]]))) =
      (some (.returned v), post)) :
    memW post l.toNat ≠ 0 := by
  rw [evaluateHOLFiniteState_seq_line780] at hr
  rcases hs : evaluateHOLFiniteState s
      (.store (.op .add [.var .local (ofString "l"), .const 8])
        (.op .add [.var .local (ofString "n"), .const 1])) with ⟨r, mid⟩
  rw [hs] at hr
  cases r with
  | none =>
    have hm := (hoare_lst_push_length_write l n).run s hc ⟨hl, hn, hb⟩
      (by rw [hs]; simp)
    rw [hs] at hm
    have hm' := hm rfl
    dsimp only at hr
    rw [evaluateHOLFiniteState_return] at hr
    split at hr
    · cases hr
    · split at hr
      · have he := (Prod.mk.inj hr).2
        subst post
        exact hm'
      · cases hr
  | some r =>
    have hs' := hs
    rw [evaluateHOLFiniteState_store] at hs'
    dsimp only at hr
    have he := (Prod.mk.inj hr).1
    cases he
    split at hs'
    · split at hs'
      · split at hs' <;> cases hs'
      · cases hs'
    · cases hs'

/-- A returned store sequence exposes a falling store with unchanged locals
and code, followed by a returned continuation. -/
theorem store_seq_returned {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {dst src : ExpHOL 64} {tail : ProgHOL 64} {v : ValueHOL 64}
    (hr : evaluateHOLFiniteState s (.seq (.store dst src) tail) =
      (some (.returned v), post)) :
    ∃ mid, evaluateHOLFiniteState s (.store dst src) = (none, mid) ∧
      mid.locals = s.locals ∧ mid.code = s.code ∧
      evaluateHOLFiniteState mid tail = (some (.returned v), post) := by
  rw [evaluateHOLFiniteState_seq_line780] at hr
  rcases hs : evaluateHOLFiniteState s (.store dst src) with ⟨r, mid⟩
  rw [hs] at hr
  have hs' := hs
  rw [evaluateHOLFiniteState_store] at hs'
  cases r with
  | none =>
    refine ⟨mid, rfl, ?_, ?_, hr⟩
    · split at hs'
      · split at hs'
        · split at hs'
          · cases hs'; rfl
          · cases hs'
        · cases hs'
      · cases hs'
    · have he := (evaluateHOLFiniteState_metadata s (.store dst src)).1
      simpa only [hs] using he
  | some r =>
    dsimp only at hr
    have he := (Prod.mk.inj hr).1
    cases he
    split at hs'
    · split at hs'
      · split at hs' <;> cases hs'
      · cases hs'
    · cases hs'

/-- A word store cannot return from its enclosing function. -/
theorem store_not_returned {F : Type} (s : PanSemStateFiniteExact 64 F)
    (dst src : ExpHOL 64) (v : ValueHOL 64) :
    (evaluateHOLFiniteState s (.store dst src)).1 ≠ some (.returned v) := by
  rw [evaluateHOLFiniteState_store]
  split
  · split
    · split <;> simp
    · simp
  · simp

/-- A returned sequence must reach its tail when the prefix cannot return. -/
theorem seq_returned_of_not_returned {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {pre tail : ProgHOL 64} {v : ValueHOL 64}
    (hp : (evaluateHOLFiniteState s pre).1 ≠ some (.returned v))
    (hr : evaluateHOLFiniteState s (.seq pre tail) = (some (.returned v), post)) :
    ∃ mid, evaluateHOLFiniteState s pre = (none, mid) ∧
      evaluateHOLFiniteState mid tail = (some (.returned v), post) := by
  rw [evaluateHOLFiniteState_seq_line780] at hr
  rcases he : evaluateHOLFiniteState s pre with ⟨r, mid⟩
  rw [he] at hr hp
  cases r with
  | none => exact ⟨mid, rfl, hr⟩
  | some r => exact (hp (congrArg Prod.fst hr)).elim

/-- Non-returning prefixes compose without inspecting successful fall-through. -/
theorem seq_not_returned {F : Type} (s : PanSemStateFiniteExact 64 F)
    (a b : ProgHOL 64) (v : ValueHOL 64)
    (ha : (evaluateHOLFiniteState s a).1 ≠ some (.returned v))
    (hb : ∀ mid : PanSemStateFiniteExact 64 F,
      (evaluateHOLFiniteState mid b).1 ≠ some (.returned v)) :
    (evaluateHOLFiniteState s (.seq a b)).1 ≠ some (.returned v) := by
  rw [evaluateHOLFiniteState_seq_line780]
  rcases he : evaluateHOLFiniteState s a with ⟨r, mid⟩
  cases r with
  | none => exact hb mid
  | some r => simpa only [he] using ha

/-- A falling word store leaves the local environment unchanged. -/
theorem store_fall_locals {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {dst src : ExpHOL 64}
    (h : evaluateHOLFiniteState s (.store dst src) = (none, post)) :
    post.locals = s.locals := by
  rw [evaluateHOLFiniteState_store] at h
  split at h
  · split at h
    · split at h
      · cases h; rfl
      · cases h
    · cases h
  · cases h

/-- Local preservation composes across falling sequences. -/
theorem seq_fall_locals {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {a b : ProgHOL 64}
    (ha : ∀ mid, evaluateHOLFiniteState s a = (none, mid) → mid.locals = s.locals)
    (hb : ∀ mid, evaluateHOLFiniteState mid b = (none, post) → post.locals = mid.locals)
    (hr : evaluateHOLFiniteState s (.seq a b) = (none, post)) :
    post.locals = s.locals := by
  rw [evaluateHOLFiniteState_seq_line780] at hr
  rcases hs : evaluateHOLFiniteState s a with ⟨r, mid⟩
  rw [hs] at hr
  cases r with
  | some r => cases hr
  | none => exact (hb mid hr).trans (ha mid hs)

/-- A successful ignored-result call restores caller locals. In particular,
the copy preceding growth stores preserves `np`, `l`, `cap`, and `n`. -/
theorem ignored_call_fall_locals {F : Type} (s mid : PanSemStateFiniteExact 64 F)
    (f : MlS) (args : List (ExpHOL 64))
    (h : evaluateHOLFiniteState s (.call (some (none, none)) f args) = (none, mid)) :
    mid.locals = s.locals ∧ mid.code = s.code := by
  have hmeta := (evaluateHOLFiniteState_metadata s (.call (some (none, none)) f args)).1
  rw [h] at hmeta
  refine ⟨?_, hmeta⟩
  revert h
  rw [evaluateHOLFiniteState_call]
  split
  · simp
  · split
    · simp
    · split
      · simp
      · rcases evaluateHOLFiniteState (callEntryStateHOLFinite s _) _ with ⟨r, st⟩
        rcases r with _ | (_ | _ | _ | _ | w | _ | _) <;> dsimp only <;>
          (repeat' split) <;> simp
        intro h; rw [← h]

/-- Ignoring a call result cannot directly return from the caller. -/
theorem ignored_call_not_returned {F : Type} (s : PanSemStateFiniteExact 64 F)
    (f : MlS) (args : List (ExpHOL 64)) (v : ValueHOL 64) :
    (evaluateHOLFiniteState s (.call (some (none, none)) f args)).1 ≠
      some (.returned v) := by
  rw [evaluateHOLFiniteState_call]
  split
  · simp
  · split
    · simp
    · split
      · simp
      · rcases evaluateHOLFiniteState (callEntryStateHOLFinite s _) _ with ⟨r, st⟩
        rcases r with _ | (_ | _ | _ | _ | w | _ | _) <;> dsimp only <;>
          (repeat' split) <;> simp

/-- Returning after an ignored-result call requires that call to fall through;
its continuation starts with the original caller locals and code. -/
theorem ignored_call_seq_returned {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {f : MlS} {args : List (ExpHOL 64)} {tail : ProgHOL 64} {v : ValueHOL 64}
    (hr : evaluateHOLFiniteState s (.seq (.call (some (none, none)) f args) tail) =
      (some (.returned v), post)) :
    ∃ mid, evaluateHOLFiniteState s (.call (some (none, none)) f args) = (none, mid) ∧
      mid.locals = s.locals ∧ mid.code = s.code ∧
      evaluateHOLFiniteState mid tail = (some (.returned v), post) := by
  rw [evaluateHOLFiniteState_seq_line780] at hr
  rcases hs : evaluateHOLFiniteState s (.call (some (none, none)) f args) with ⟨r, mid⟩
  rw [hs] at hr
  cases r with
  | none =>
    obtain ⟨hl, hc⟩ := ignored_call_fall_locals s mid f args hs
    exact ⟨mid, rfl, hl, hc, hr⟩
  | some r =>
    have hn := ignored_call_not_returned s f args v
    rw [hs] at hn
    exact (hn (congrArg Prod.fst hr)).elim

/-- The growth branch's data, capacity, and length writes compose with return
to establish nonzero backing from the allocator result. -/
theorem lst_push_growth_writes_backing_nonzero {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (l n cap np : BitVec 64) (v : ValueHOL 64)
    (hc : s.code = originalRuntimeCode)
    (hl : s.locals.lookup (ofString "l") = some (.val (.word l)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (hcap : s.locals.lookup (ofString "cap") = some (.val (.word cap)))
    (hnp : s.locals.lookup (ofString "np") = some (.val (.word np)))
    (hnz : np.toNat ≠ 0)
    (hr : evaluateHOLFiniteState s
      (.seq (.store (.op .add [.var .local (ofString "l"), .const 0])
          (.var .local (ofString "np")))
        (.seq (.store (.op .add [.var .local (ofString "l"), .const 16])
            (.panop .mul [.var .local (ofString "cap"), .const 2]))
          (.seq (.store (.op .add [.var .local (ofString "l"), .const 8])
              (.op .add [.var .local (ofString "n"), .const 1]))
            (.return (.op .add
              [.load .one (.op .add [.var .local (ofString "l"), .const 0]),
               .panop .mul [.var .local (ofString "n"), .var .local (ofString "esz")]]))))) =
      (some (.returned v), post)) : memW post l.toNat ≠ 0 := by
  obtain ⟨mid, hs, hloc, hcode, ht⟩ := store_seq_returned hr
  have hm := (hoare_lst_push_data_write l).run s hc ⟨hl, np, hnp, hnz⟩
    (by rw [hs]; simp)
  rw [hs] at hm
  have hml : mid.locals.lookup (ofString "l") = some (.val (.word l)) := by
    rw [hloc]; exact hl
  have hmc : mid.locals.lookup (ofString "cap") = some (.val (.word cap)) := by
    rw [hloc]; exact hcap
  obtain ⟨last, hs2, hloc2, hcode2, ht2⟩ := store_seq_returned ht
  have hm2 := (hoare_lst_push_capacity_write l cap).run mid (hcode.trans hc)
    ⟨hml, hmc, hm rfl⟩ (by rw [hs2]; simp)
  rw [hs2] at hm2
  exact lst_push_tail_backing_nonzero last post l n v (hcode2.trans (hcode.trans hc))
    (by rw [hloc2, hloc]; exact hl) (by rw [hloc2, hloc]; exact hn) (hm2 rfl) ht2

/-- Reassociate the growth branch's two stores with the common tail without
changing execution, including any non-falling result. -/
theorem evaluate_seq_assoc {F : Type} (s : PanSemStateFiniteExact 64 F)
    (a b c : ProgHOL 64) :
    evaluateHOLFiniteState s (.seq (.seq a b) c) =
      evaluateHOLFiniteState s (.seq a (.seq b c)) := by
  simp only [evaluateHOLFiniteState_seq_line780]
  rcases ha : evaluateHOLFiniteState s a with ⟨r, mid⟩
  cases r <;> simp only

/-- The exact grouped growth-store suffix of `lst_push` retains the new
nonzero backing through the shared length update and return. -/
theorem lst_push_grouped_growth_backing_nonzero {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (l n cap np : BitVec 64) (v : ValueHOL 64)
    (hc : s.code = originalRuntimeCode)
    (hl : s.locals.lookup (ofString "l") = some (.val (.word l)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (hcap : s.locals.lookup (ofString "cap") = some (.val (.word cap)))
    (hnp : s.locals.lookup (ofString "np") = some (.val (.word np)))
    (hnz : np.toNat ≠ 0)
    (hr : evaluateHOLFiniteState s
      (.seq (.seq
          (.store (.op .add [.var .local (ofString "l"), .const 0])
            (.var .local (ofString "np")))
          (.store (.op .add [.var .local (ofString "l"), .const 16])
            (.panop .mul [.var .local (ofString "cap"), .const 2])))
        (.seq (.store (.op .add [.var .local (ofString "l"), .const 8])
            (.op .add [.var .local (ofString "n"), .const 1]))
          (.return (.op .add
            [.load .one (.op .add [.var .local (ofString "l"), .const 0]),
             .panop .mul [.var .local (ofString "n"), .var .local (ofString "esz")]])))) =
      (some (.returned v), post)) : memW post l.toNat ≠ 0 := by
  rw [evaluate_seq_assoc] at hr
  exact lst_push_growth_writes_backing_nonzero s post l n cap np v
    hc hl hn hcap hnp hnz hr

/-- On fall-through, the growth stores have installed nonzero backing before
the allocation declaration restores its local scope. -/
theorem lst_push_growth_stores_fall {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (l cap np : BitVec 64)
    (hc : s.code = originalRuntimeCode)
    (hl : s.locals.lookup (ofString "l") = some (.val (.word l)))
    (hcap : s.locals.lookup (ofString "cap") = some (.val (.word cap)))
    (hnp : s.locals.lookup (ofString "np") = some (.val (.word np)))
    (hnz : np.toNat ≠ 0)
    (hr : evaluateHOLFiniteState s
      (.seq (.store (.op .add [.var .local (ofString "l"), .const 0])
          (.var .local (ofString "np")))
        (.store (.op .add [.var .local (ofString "l"), .const 16])
          (.panop .mul [.var .local (ofString "cap"), .const 2]))) = (none, post)) :
    memW post l.toNat ≠ 0 := by
  rw [evaluateHOLFiniteState_seq_line780] at hr
  rcases hs : evaluateHOLFiniteState s
    (.store (.op .add [.var .local (ofString "l"), .const 0])
      (.var .local (ofString "np"))) with ⟨r, mid⟩
  rw [hs] at hr
  cases r with
  | some r => cases hr
  | none =>
    dsimp only at hr
    have hm := (hoare_lst_push_data_write l).run s hc ⟨hl, np, hnp, hnz⟩
      (by rw [hs]; simp)
    rw [hs] at hm
    have hloc : mid.locals = s.locals := by
      rw [evaluateHOLFiniteState_store] at hs
      split at hs
      · split at hs
        · split at hs
          · cases hs; rfl
          · cases hs
        · cases hs
      · cases hs
    have hcode := (evaluateHOLFiniteState_metadata s
      (.store (.op .add [.var .local (ofString "l"), .const 0])
        (.var .local (ofString "np")))).1
    rw [hs] at hcode
    have hm2 := (hoare_lst_push_capacity_write l cap).run mid (hcode.trans hc)
      ⟨by rw [hloc]; exact hl, by rw [hloc]; exact hcap, hm rfl⟩
      (by rw [hr]; simp)
    rw [hr] at hm2
    exact hm2 rfl

/-- The allocation declaration's concrete copy-and-store body establishes
nonzero backing whenever it falls through. -/
theorem lst_push_copy_stores_fall {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (l cap np : BitVec 64)
    (hc : s.code = originalRuntimeCode)
    (hl : s.locals.lookup (ofString "l") = some (.val (.word l)))
    (hcap : s.locals.lookup (ofString "cap") = some (.val (.word cap)))
    (hnp : s.locals.lookup (ofString "np") = some (.val (.word np)))
    (hnz : np.toNat ≠ 0)
    (hr : evaluateHOLFiniteState s
      (.seq
        (.call (some (none, none)) (ofString "memcpy")
          [.var .local (ofString "np"),
           .load .one (.op .add [.var .local (ofString "l"), .const 0]),
           .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]])
        (.seq
          (.store (.op .add [.var .local (ofString "l"), .const 0])
            (.var .local (ofString "np")))
          (.store (.op .add [.var .local (ofString "l"), .const 16])
            (.panop .mul [.var .local (ofString "cap"), .const 2])))) = (none, post)) :
    memW post l.toNat ≠ 0 := by
  rw [evaluateHOLFiniteState_seq_line780] at hr
  rcases hs : evaluateHOLFiniteState s
    (.call (some (none, none)) (ofString "memcpy")
      [.var .local (ofString "np"),
       .load .one (.op .add [.var .local (ofString "l"), .const 0]),
       .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]]) with ⟨r, mid⟩
  rw [hs] at hr
  cases r with
  | some r => cases hr
  | none =>
    obtain ⟨hlocal, hcode⟩ := ignored_call_fall_locals s mid _ _ hs
    exact lst_push_growth_stores_fall mid post l cap np (hcode.trans hc)
      (by rw [hlocal]; exact hl) (by rw [hlocal]; exact hcap)
      (by rw [hlocal]; exact hnp) hnz hr

/-- The concrete copy followed by growth stores and the common return tail
establishes nonzero backing from the allocator result in `np`. -/
theorem lst_push_copy_growth_backing_nonzero {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (l n cap np : BitVec 64) (v : ValueHOL 64)
    (hc : s.code = originalRuntimeCode)
    (hl : s.locals.lookup (ofString "l") = some (.val (.word l)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (hcap : s.locals.lookup (ofString "cap") = some (.val (.word cap)))
    (hnp : s.locals.lookup (ofString "np") = some (.val (.word np)))
    (hnz : np.toNat ≠ 0)
    (hr : evaluateHOLFiniteState s
      (.seq (.seq
        (.call (some (none, none)) (ofString "memcpy")
          [.var .local (ofString "np"),
           .load .one (.op .add [.var .local (ofString "l"), .const 0]),
           .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]])
        (.seq
          (.store (.op .add [.var .local (ofString "l"), .const 0])
            (.var .local (ofString "np")))
          (.store (.op .add [.var .local (ofString "l"), .const 16])
            (.panop .mul [.var .local (ofString "cap"), .const 2]))))
        (.seq (.store (.op .add [.var .local (ofString "l"), .const 8])
            (.op .add [.var .local (ofString "n"), .const 1]))
          (.return (.op .add
            [.load .one (.op .add [.var .local (ofString "l"), .const 0]),
             .panop .mul [.var .local (ofString "n"), .var .local (ofString "esz")]])))) =
      (some (.returned v), post)) : memW post l.toNat ≠ 0 := by
  rw [evaluate_seq_assoc] at hr
  obtain ⟨mid, _, hloc, hcode, ht⟩ := ignored_call_seq_returned hr
  exact lst_push_grouped_growth_backing_nonzero mid post l n cap np v
    (hcode.trans hc) (by rw [hloc]; exact hl) (by rw [hloc]; exact hn)
    (by rw [hloc]; exact hcap) (by rw [hloc]; exact hnp) hnz ht

/-- A fresh backing block starts above the positive source base. -/
theorem fresh_backing_nonzero {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {p n : Nat} (hA : ArenaOK s) (hf : FreshBlock s post p n) : p ≠ 0 := by
  have hlo := hA.1.trans hf.2.1.1
  have hbase : 0 < sourceBase := by decide
  omega

/-- The growth branch stores the old heap frontier in the list's data word.
This is the `hnp_eq`/`hl0_post` pair established by the concrete push proof. -/
theorem backing_nonzero_of_grow {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {l np : Nat}
    (hA : ArenaOK s) (hnp : np = globN s "heap_ptr")
    (hdata : memW post l = np) : memW post l ≠ 0 := by
  have hbase : 0 < sourceBase := by decide
  have hlo := hA.1
  rw [hdata, hnp]
  omega

/-- Expose a falling declaration call and its scope-restored continuation.
The memory is unchanged by restoration of the declared local. -/
theorem dec_call_fall_inv {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {x fname : MlS} {sh : ShapeHOL} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (h : evaluateHOLFiniteState s (.decCall x sh fname args cont) = (none, t)) :
    ∃ values body callee retShape rv post u,
      lookupCodeHOLFinite s.code.lookup fname values = some (body, callee, retShape) ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned rv), post) ∧
      evaluateHOLFiniteState (setVarHOLFinite x rv { post with locals := s.locals }) cont = (none, u) ∧
      t.memory = u.memory ∧
      (∀ k, k ≠ x → t.locals.lookup k = u.locals.lookup k) := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · rename_i values hargs body callee retShape hl
      split at h
      · simp at h
      · dsimp only at h
        rcases hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨r, post⟩
        rw [hr] at h
        cases r with
        | none => simp at h
        | some r =>
          cases r with
          | returned rv =>
            dsimp only at h
            split at h
            · rcases ht : evaluateHOLFiniteState
                (setVarHOLFinite x rv { post with locals := s.locals }) cont with ⟨rc, u⟩
              rw [ht] at h
              cases rc with
              | none =>
                have he := (Prod.mk.inj h).2
                exact ⟨_, body, callee, retShape, rv, post, u, hl, hr, ht,
                  congrArg (fun st => st.memory) he.symm, by
                    intro k hk
                    rw [← he]
                    cases s.locals.lookup x <;>
                      simp [HolFiniteMapExact.resVarEq, HolFiniteMapExact.lookup_eraseEq,
                        HolFiniteMapExact.lookup_updateEq, FDOMSUB_HOL, FUPDATE_HOL,
                        hk, Ne.symm hk]⟩
              | some r => simp at h
            · simp at h
          | _ => simp at h

/-- A scoped call can return only through its continuation. -/
theorem dec_call_not_returned {F : Type} (s : PanSemStateFiniteExact 64 F)
    (x fname : MlS) (sh : ShapeHOL) (args : List (ExpHOL 64)) (cont : ProgHOL 64)
    (v : ValueHOL 64)
    (hc : ∀ a : PanSemStateFiniteExact 64 F,
      (evaluateHOLFiniteState a cont).1 ≠ some (.returned v)) :
    (evaluateHOLFiniteState s (.decCall x sh fname args cont)).1 ≠
      some (.returned v) := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
  split
  · simp
  · split
    · simp
    · split
      · simp
      · dsimp only
        rcases evaluateHOLFiniteState (callEntryStateHOLFinite s _) _ with ⟨r, post⟩
        cases r with
        | none => simp
        | some r =>
          cases r with
          | returned rv =>
            dsimp only
            split
            · simpa only using hc (setVarHOLFinite x rv {post with locals := s.locals})
            · simp
          | _ => simp

/-- The existing allocator return contract supplies the nonzero word needed
by the concrete growth stores, including for a zero-sized request. -/
theorem alloc_return_nonzero (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode)
    (hA : ArenaReady (callEntryStateHOLFinite s callee))
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "alloc") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    ∃ np : BitVec 64, v = .val (.word np) ∧ np.toNat ≠ 0 ∧ ArenaReady post := by
  have ha := funSpec_at_lookup h.rt_alloc s hc vs body callee ret hl hA
    (by rw [hr]; simp)
  rw [hr] at ha
  obtain ⟨np, hv, hpost, _, hf⟩ := ha v rfl
  exact ⟨np, hv, fresh_backing_nonzero hA.2 hf, hpost⟩

/-- A declaration whose continuation preserves locals preserves every local
other than its temporary binding across the whole call. -/
theorem dec_call_fall_lookup {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {x fname : MlS} {sh : ShapeHOL} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hcont : ∀ (a b : PanSemStateFiniteExact 64 F),
      evaluateHOLFiniteState a cont = (none, b) → b.locals = a.locals)
    (hr : evaluateHOLFiniteState s (.decCall x sh fname args cont) = (none, post))
    (k : MlS) (hk : k ≠ x) : post.locals.lookup k = s.locals.lookup k := by
  obtain ⟨_, _, _, _, rv, allocated, done, _, _, hrun, _, hlocal⟩ := dec_call_fall_inv hr
  rw [hlocal k hk, hcont _ _ hrun]
  simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hk, Ne.symm hk]

/-- The complete allocating branch establishes nonzero backing, including
copying and restoration of the temporary `np` local. -/
theorem lst_push_alloc_branch_fall (h : PtxCallees) {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (l cap : BitVec 64)
    (hc : s.code = originalRuntimeCode) (hA : ArenaReady s)
    (hl : s.locals.lookup (ofString "l") = some (.val (.word l)))
    (hcap : s.locals.lookup (ofString "cap") = some (.val (.word cap)))
    (hr : evaluateHOLFiniteState s
      (.decCall (ofString "np") .one (ofString "alloc")
        [.panop .mul [.panop .mul
          [.var .local (ofString "esz"), .var .local (ofString "cap")], .const 2]]
        (.seq
          (.call (some (none, none)) (ofString "memcpy")
            [.var .local (ofString "np"),
             .load .one (.op .add [.var .local (ofString "l"), .const 0]),
             .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]])
          (.seq
            (.store (.op .add [.var .local (ofString "l"), .const 0])
              (.var .local (ofString "np")))
            (.store (.op .add [.var .local (ofString "l"), .const 16])
              (.panop .mul [.var .local (ofString "cap"), .const 2]))))) = (none, post)) :
    memW post l.toNat ≠ 0 := by
  obtain ⟨vs, body, callee, ret, rv, allocated, done, hlookup, hrun, hcont, hmem, _⟩ :=
    dec_call_fall_inv hr
  have hentry : ArenaReady (callEntryStateHOLFinite s callee) :=
    (arenaReady_with_locals s callee (s.clock - 1)).2 hA
  obtain ⟨np, rfl, hnz, hpost⟩ :=
    alloc_return_nonzero h s vs body callee ret rv allocated hc hentry hlookup hrun
  have hb := lst_push_copy_stores_fall
    (setVarHOLFinite (ofString "np") (.val (.word np)) { allocated with locals := s.locals })
    done l cap np hpost.1.code
    (by simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "np" ≠ ofString "l" by decide] using hl)
    (by simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "np" ≠ ofString "cap" by decide] using hcap)
    (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]) hnz hcont
  simpa only [memW, hmem] using hb

/-- The allocating branch preserves all caller lookups except its temporary
`np` binding; in particular it preserves the list address and old length. -/
theorem lst_push_alloc_branch_lookup {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (args : List (ExpHOL 64))
    (hr : evaluateHOLFiniteState s
      (.decCall (ofString "np") .one (ofString "alloc") args
        (.seq
          (.call (some (none, none)) (ofString "memcpy")
            [.var .local (ofString "np"),
             .load .one (.op .add [.var .local (ofString "l"), .const 0]),
             .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]])
          (.seq
            (.store (.op .add [.var .local (ofString "l"), .const 0])
              (.var .local (ofString "np")))
            (.store (.op .add [.var .local (ofString "l"), .const 16])
              (.panop .mul [.var .local (ofString "cap"), .const 2]))))) = (none, post))
    (k : MlS) (hk : k ≠ ofString "np") : post.locals.lookup k = s.locals.lookup k := by
  apply dec_call_fall_lookup ?_ hr k hk
  intro a b hab
  apply seq_fall_locals ?_ ?_ hab
  · intro mid hm
    exact (ignored_call_fall_locals a mid _ _ hm).1
  · intro mid hm
    exact seq_fall_locals (fun _ hs => store_fall_locals hs)
      (fun _ hs => store_fall_locals hs) hm

/-- A falling conditional either executes its growth branch or skips it.
This exposes the branch result without imposing a condition-evaluation premise. -/
theorem ite_skip_fall_inv {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {cond : ExpHOL 64} {grow : ProgHOL 64}
    (hr : evaluateHOLFiniteState s (.ite cond grow .skip) = (none, post)) :
    evaluateHOLFiniteState s grow = (none, post) ∨ post = s := by
  rw [evaluateHOLFiniteState_ite] at hr
  split at hr
  · split at hr
    · rw [evaluateHOLFiniteState_skip] at hr
      exact Or.inr (Prod.mk.inj hr).2.symm
    · exact Or.inl hr
  · cases hr

/-- Both outcomes of the capacity check preserve nonzero backing. The growth
case obtains it from allocation; the skip case retains the entry fact. -/
theorem lst_push_capacity_branch_fall (h : PtxCallees) {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (l cap : BitVec 64)
    (hc : s.code = originalRuntimeCode) (hA : ArenaReady s)
    (hl : s.locals.lookup (ofString "l") = some (.val (.word l)))
    (hcap : s.locals.lookup (ofString "cap") = some (.val (.word cap)))
    (hb : memW s l.toNat ≠ 0)
    (cond : ExpHOL 64)
    (hr : evaluateHOLFiniteState s
      (.ite cond
        (.decCall (ofString "np") .one (ofString "alloc")
          [.panop .mul [.panop .mul
            [.var .local (ofString "esz"), .var .local (ofString "cap")], .const 2]]
          (.seq
            (.call (some (none, none)) (ofString "memcpy")
              [.var .local (ofString "np"),
               .load .one (.op .add [.var .local (ofString "l"), .const 0]),
               .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]])
            (.seq
              (.store (.op .add [.var .local (ofString "l"), .const 0])
                (.var .local (ofString "np")))
              (.store (.op .add [.var .local (ofString "l"), .const 16])
                (.panop .mul [.var .local (ofString "cap"), .const 2]))))) .skip) =
      (none, post)) : memW post l.toNat ≠ 0 ∧
        (∀ k, k ≠ ofString "np" → post.locals.lookup k = s.locals.lookup k) := by
  rcases ite_skip_fall_inv hr with hg | rfl
  · exact ⟨lst_push_alloc_branch_fall h s post l cap hc hA hl hcap hg,
      fun k hk => lst_push_alloc_branch_lookup s post _ hg k hk⟩
  · exact ⟨hb, fun _ _ => rfl⟩

/-- A falling capacity branch supplies precisely the backing and local facts
needed by the common tail. -/
theorem lst_push_branch_to_tail {F : Type}
    (s mid post : PanSemStateFiniteExact 64 F) (l n : BitVec 64) (v : ValueHOL 64)
    (branch : ProgHOL 64) (hc : s.code = originalRuntimeCode)
    (hbranch : evaluateHOLFiniteState s branch = (none, mid))
    (hb : memW mid l.toNat ≠ 0)
    (hl : mid.locals.lookup (ofString "l") = s.locals.lookup (ofString "l"))
    (hn : mid.locals.lookup (ofString "n") = s.locals.lookup (ofString "n"))
    (hsl : s.locals.lookup (ofString "l") = some (.val (.word l)))
    (hsn : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (hr : evaluateHOLFiniteState s
      (.seq branch
        (.seq (.store (.op .add [.var .local (ofString "l"), .const 8])
          (.op .add [.var .local (ofString "n"), .const 1]))
          (.return (.op .add
            [.load .one (.op .add [.var .local (ofString "l"), .const 0]),
             .panop .mul [.var .local (ofString "n"), .var .local (ofString "esz")]])))) =
      (some (.returned v), post)) : memW post l.toNat ≠ 0 := by
  have hm := (evaluateHOLFiniteState_metadata s branch).1
  rw [hbranch] at hm
  rw [evaluateHOLFiniteState_seq_line780, hbranch] at hr
  exact lst_push_tail_backing_nonzero mid post l n v (hm.trans hc)
    (hl.trans hsl) (hn.trans hsn) hb hr

/-- A conditional cannot return if neither arm can return. -/
theorem ite_not_returned {F : Type} (s : PanSemStateFiniteExact 64 F)
    (cond : ExpHOL 64) (a b : ProgHOL 64) (v : ValueHOL 64)
    (ha : (evaluateHOLFiniteState s a).1 ≠ some (.returned v))
    (hb : (evaluateHOLFiniteState s b).1 ≠ some (.returned v)) :
    (evaluateHOLFiniteState s (.ite cond a b)).1 ≠ some (.returned v) := by
  rw [evaluateHOLFiniteState_ite]
  split
  · split
    · exact hb
    · exact ha
  · simp

/-- The complete returned push suffix forces the capacity branch to fall
through, then preserves its nonzero data word through the common tail. -/
theorem lst_push_capacity_tail_returned (h : PtxCallees) {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (l n cap : BitVec 64) (v : ValueHOL 64)
    (hc : s.code = originalRuntimeCode) (hA : ArenaReady s)
    (hl : s.locals.lookup (ofString "l") = some (.val (.word l)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (hcap : s.locals.lookup (ofString "cap") = some (.val (.word cap)))
    (hb : memW s l.toNat ≠ 0)
    (hr : evaluateHOLFiniteState s
      (.seq
        (.ite (.cmp .notLower (.var .local (ofString "n")) (.var .local (ofString "cap")))
          (.decCall (ofString "np") .one (ofString "alloc")
            [.panop .mul [.panop .mul
              [.var .local (ofString "esz"), .var .local (ofString "cap")], .const 2]]
            (.seq
              (.call (some (none, none)) (ofString "memcpy")
                [.var .local (ofString "np"),
                 .load .one (.op .add [.var .local (ofString "l"), .const 0]),
                 .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]])
              (.seq
                (.store (.op .add [.var .local (ofString "l"), .const 0])
                  (.var .local (ofString "np")))
                (.store (.op .add [.var .local (ofString "l"), .const 16])
                  (.panop .mul [.var .local (ofString "cap"), .const 2]))))) .skip)
        (.seq (.store (.op .add [.var .local (ofString "l"), .const 8])
          (.op .add [.var .local (ofString "n"), .const 1]))
          (.return (.op .add
            [.load .one (.op .add [.var .local (ofString "l"), .const 0]),
             .panop .mul [.var .local (ofString "n"), .var .local (ofString "esz")]])))) =
      (some (.returned v), post)) : memW post l.toNat ≠ 0 := by
  obtain ⟨mid, hm, _⟩ := seq_returned_of_not_returned (by
    apply ite_not_returned
    · apply dec_call_not_returned
      intro a
      apply seq_not_returned
      · exact ignored_call_not_returned _ _ _ _
      · intro b
        apply seq_not_returned
        · exact store_not_returned _ _ _ _
        · intro c; exact store_not_returned _ _ _ _
    · simp [evaluateHOLFiniteState_skip]) hr
  obtain ⟨hbmid, hlocals⟩ := lst_push_capacity_branch_fall h s mid l cap hc hA hl hcap hb _ hm
  exact lst_push_branch_to_tail s mid post l n v _ hc hm hbmid
    (hlocals _ (by decide)) (hlocals _ (by decide)) hl hn hr

/-- A returning word declaration exposes a word-valued initializer and the
returned continuation; scope restoration does not change memory. -/
theorem dec_word_returned_inv {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {x : MlS} {e : ExpHOL 64} {cont : ProgHOL 64} {v : ValueHOL 64}
    (hr : evaluateHOLFiniteState s (.dec x .one e cont) = (some (.returned v), post)) :
    ∃ w : BitVec 64, ∃ mid,
      evaluateHOLFiniteState (setVarHOLFinite x (.val (.word w)) s) cont =
        (some (.returned v), mid) ∧ post.memory = mid.memory := by
  rw [evaluateHOLFiniteState_dec_total] at hr
  dsimp only at hr
  split at hr
  · cases hr
  · rename_i value he
    split at hr
    · rename_i hshape
      have hw : ∃ w : BitVec 64, value = .val (.word w) := by
        cases value with
        | val z => cases z with
          | word w => exact ⟨w, rfl⟩
        | _ => simp [shapeOfHOLExact, shapeEqHOL] at hshape
      obtain ⟨w, rfl⟩ := hw
      rcases he : evaluateHOLFiniteState (setVarHOLFinite x (.val (.word w)) s) cont with ⟨r, mid⟩
      rw [he] at hr
      exact ⟨w, mid, by rw [← (Prod.mk.inj hr).1]; exact he,
        congrArg (fun t => t.memory) (Prod.mk.inj hr).2.symm⟩
    · cases hr

/-- The entire concrete push body preserves a nonzero backing word. The two
header reads are exposed from the returned execution, without extra evaluation
or branch-selection premises. -/
theorem lst_push_body_backing_nonzero (h : PtxCallees) {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (l : BitVec 64) (v : ValueHOL 64)
    (hc : s.code = originalRuntimeCode) (hA : ArenaReady s)
    (hl : s.locals.lookup (ofString "l") = some (.val (.word l)))
    (hb : memW s l.toNat ≠ 0)
    (hr : evaluateHOLFiniteState s (sourceFunctionEntry Guest.Software.guestFn_lst_push).2.2.1 =
      (some (.returned v), post)) : memW post l.toNat ≠ 0 := by
  dsimp only [sourceFunctionEntry, Guest.Software.guestFn_lst_push,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map] at hr
  obtain ⟨n, mid, hr, hm⟩ := dec_word_returned_inv hr
  obtain ⟨cap, last, hr, hm'⟩ := dec_word_returned_inv hr
  have hs := lst_push_capacity_tail_returned h
    (setVarHOLFinite (ofString "cap") (.val (.word cap))
      (setVarHOLFinite (ofString "n") (.val (.word n)) s)) last l n cap v hc
    ((arenaReady_with_locals s _ s.clock).mpr hA) (by
      simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl,
        show ofString "cap" ≠ ofString "l" by decide,
        show ofString "n" ≠ ofString "l" by decide])
    (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "cap" ≠ ofString "n" by decide])
    (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]) hb hr
  simpa only [memW, hm, hm'] using hs

/-- A push may relocate either backing array. Preserve the outer header
pointers, and allow each data word either to stay fixed or to become a fresh
heap pointer. This also records preservation of the list not being pushed. -/
theorem txBacking_of_kept_or_grown_headers {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) (h : TxBacking s)
    (hbo : globN post "bo" = globN s "bo")
    (hslots : ∀ k ∈ ([40, 72] : List Nat),
      memW post (globN s "bo" + k) = memW s (globN s "bo" + k))
    (hdata : ∀ k ∈ ([40, 72] : List Nat),
      memW post (memW s (globN s "bo" + k)) = memW s (memW s (globN s "bo" + k)) ∨
      globN s "heap_ptr" ≤ memW post (memW s (globN s "bo" + k))) :
    TxBacking post := by
  have hn : ∀ k ∈ ([40, 72] : List Nat),
      memW post (memW s (globN s "bo" + k)) ≠ 0 := by
    intro k hk
    rcases hdata k hk with he | hg
    · rw [he]
      have hk' : k = 40 ∨ k = 72 := by simpa using hk
      rcases hk' with rfl | rfl
      · exact h.1
      · exact h.2
    · have hlo := hA.1.trans hg
      have hbase : 0 < sourceBase := by decide
      omega
  constructor
  · rw [hbo, hslots 40 (by simp)]
    exact hn 40 (by simp)
  · rw [hbo, hslots 72 (by simp)]
    exact hn 72 (by simp)

/-- Initialization bridge for the two `execute_block` list allocations. The
freshness witnesses may have different allocation-entry states. -/
theorem txBacking_of_fresh_lists {F : Type}
    {s40 s72 post : PanSemStateFiniteExact 64 F}
    (h40 : ArenaOK s40) (h72 : ArenaOK s72)
    (hf40 : FreshBlock s40 post (memW post (memW post (globN post "bo" + 40))) 128)
    (hf72 : FreshBlock s72 post (memW post (memW post (globN post "bo" + 72))) 128) :
    TxBacking post :=
  ⟨fresh_backing_nonzero h40 hf40, fresh_backing_nonzero h72 hf72⟩

/-- Growth replaces a backing pointer by a fresh allocation; the no-growth
branch retains the previous pointer. Both branches preserve nonzeroness. -/
theorem backing_nonzero_of_kept_or_fresh {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {l n : Nat}
    (hA : ArenaOK s) (hn : memW s l ≠ 0)
    (hstep : memW post l = memW s l ∨ FreshBlock s post (memW post l) n) :
    memW post l ≠ 0 := by
  rcases hstep with he | hf
  · rwa [he]
  · exact fresh_backing_nonzero hA hf

/-- The concrete account proof supplies the scratch frontier bound omitted by
the weaker `PtxCallees.wk_create_ether` interface. -/
theorem create_ether_allocatorGrows {F : Type} (s : PanSemStateFiniteExact 64 F)
    (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (hc : s.code = originalRuntimeCode)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "create_ether") vs =
      some (body, callee, ret))
    (hW : WorldOK (callEntryStateHOLFinite s callee))
    (hnt : (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).1 ≠
      some .timeOut)
    (hr : Resumes (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).1) :
    AllocatorGrows (callEntryStateHOLFinite s callee)
      (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).2 := by
  have hw := funSpec_at_lookup EvmEkFk.wkSc_create_ether s hc vs body callee ret hl hW hnt hr
  exact ⟨hw.1.2.1, hw.2⟩

/-- Receipt encoding's frozen guard asks for placement even for an empty array.
The allocator-created backing buffer supplies it independently of live cells. -/
theorem logsLiveOwned_disjFixed {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {logs : Nat} (hd : LogsLiveOwned s S Nd logs) :
    LogsDisjFixed s logs := by
  by_cases hn : logs = 0
  · exact Or.inl hn
  refine Or.inr ⟨?_, ?_⟩
  · exact (hd hn).1
  · intro o ho j hj
    have hjw : j ∈ worldOwned s S Nd := by
      unfold worldOwned
      simp only [List.mem_append]
      exact Or.inl (Or.inr hj)
    rcases List.mem_append.mp ho with hh | he
    · exact (hd hn).2.1 o hh j hjw
    · obtain ⟨i, hi, ho⟩ := List.mem_flatMap.mp he
      exact (hd hn).2.2 i (List.mem_range.mp hi) o ho j hjw

/-- Allocated scratch survives a framed step just like allocated heap. The
scratch frontier must be retained (or move down), not equal `scratchEnd`. -/
theorem allocated_ivl_survives_step {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {old new R : List Ivl} {b : Ivl}
    (hAs : ArenaOK s) (hAp : ArenaOK post) (hgrow : AllocatorGrows s post)
    (hold0 : ∀ j ∈ old, j.2 = 0 → j.1 % 8 = 0)
    (hR0 : ∀ j ∈ R, j.2 = 0 → j.1 % 8 = 0)
    (hog : OwnedGrows s post old new)
    (hfr : FrameOutside s post (old ++ R ++ [freeGap s]) (heapFree s))
    (hb1 : b.1 % 8 = 0) (hb2 : b.2 % 8 = 0)
    (hb : Allocated s b) (hold : ∀ j ∈ old, Disj b j)
    (hR : ∀ j ∈ R, Disj b j) :
    Allocated post b ∧ (∀ o ∈ new, Disj b o) ∧ IvlUnhit s post b := by
  refine ⟨hgrow.allocated hb, ?_⟩
  rcases hb with hh | hs
  · exact (R13Shards.heap_ivl_survives_step hAs hgrow.1 hold0 hR0 hog hfr
      hb1 hb2 hh hold hR).2
  have hsep : heapLimit ≤ scratchStart := by decide
  have hfm := hAs.2.2.1
  have hsc := hAs.2.2.2.1
  have hhp := hAs.2.1
  have hhpp := hAp.2.1
  constructor
  · intro o ho
    rcases hog o ho with rfl | ⟨j, hj, hin⟩ | hfresh
    · exact R13Shards.disj_zero_right b
    · exact R13Shards.disj_of_inside_right hin (hold j hj)
    · exact Or.inr (Or.inr (Or.inr (by have := hs.1; have := hfresh.2; omega)))
  · intro a ha8 hhit
    obtain ⟨hc1, hc2⟩ := hhit
    have ha_in : b.1 ≤ a.toNat ∧ a.toNat + 8 ≤ b.1 + b.2 := by omega
    apply hfr a
    · intro j hj hcj
      rcases List.mem_append.mp hj with hj12 | hfg
      · rcases List.mem_append.mp hj12 with ho | hr
        · exact R13Shards.not_cellHits_of_disj ha8 (hold0 j ho) ha_in (hold j ho) hcj
        · exact R13Shards.not_cellHits_of_disj ha8 (hR0 j hr) ha_in (hR j hr) hcj
      · simp only [List.mem_singleton] at hfg
        subst j
        obtain ⟨hj1, hj2⟩ := hcj
        unfold freeGap at hj1 hj2
        have := hs.1
        dsimp at hj1 hj2
        omega
    · intro hcf
      obtain ⟨hf1, hf2⟩ := hcf
      unfold heapFree at hf1 hf2
      have := hs.1
      dsimp at hf1 hf2
      omega

/-- Separation from newly owned world storage needs placement, but no cell
alignment. This also covers byte-sized log payload intervals. -/
theorem allocated_disj_ownedGrows {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {old new : List Ivl} {b : Ivl}
    (hAs : ArenaOK s) (hAp : ArenaOK post) (hb : Allocated s b)
    (hog : OwnedGrows s post old new) (hd : ∀ j ∈ old, Disj b j) :
    ∀ o ∈ new, Disj b o := by
  intro o ho
  rcases hog o ho with rfl | ⟨j, hj, hin⟩ | hfresh
  · exact R13Shards.disj_zero_right b
  · exact R13Shards.disj_of_inside_right hin (hd j hj)
  · rcases hb with hh | hs
    · exact Or.inr (Or.inr (Or.inl (hh.2.trans hfresh.1)))
    · have hsep : heapLimit ≤ scratchStart := by decide
      have hfm := hAs.2.2.1
      have hsc := hAs.2.2.2.1
      have hhp := hAp.2.1
      exact Or.inr (Or.inr (Or.inr (by have := hs.1; have := hfresh.2; omega)))

/-- All four log intervals are heap-resident, including the byte payloads. -/
theorem logEntryOK_record_placed {F : Type} {s : PanSemStateFiniteExact 64 F}
    {log : Nat} (hl : LogEntryOK s log) :
    ∀ o ∈ logRecordIvls s log, Inside o sourceBase (globN s "heap_ptr") := by
  intro o ho
  simp only [logRecordIvls, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl
  · exact hl.2.1
  · exact hl.2.2.2.2.1
  · exact hl.2.2.2.2.2.1
  · exact hl.2.2.2.2.2.2

/-- Framing the record fixes the payload intervals used by the receipt guard.
The shared system address is filtered identically when its global is retained. -/
theorem logOwnedIvls_eq_of_unhit {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {log : Nat}
    (hAs : ArenaOK s) (hl : LogEntryOK s log)
    (hu : IvlUnhit s post (log, 40))
    (hsys : globN post "vm_system_address" = globN s "vm_system_address") :
    logOwnedIvls post log = logOwnedIvls s log := by
  have hb := (R13Shards.ivl_allocated_bound hAs (Or.inl hl.2.1)).2
  have ha := hl.1.1
  have hm : ∀ k ∈ ([0, 8, 16, 24, 32] : List Nat),
      memW post (log + k) = memW s (log + k) := by
    intro k hk
    apply R13Shards.memW_eq_of_ivlUnhit hu
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> omega
    · exact hb
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> (constructor <;> omega)
  have h0 : memW post log = memW s log := by simpa using hm 0 (by simp)
  simp only [logOwnedIvls, logRecordIvls, hsys, h0,
    hm 8 (by simp), hm 16 (by simp), hm 24 (by simp), hm 32 (by simp)]

theorem logOwnedIvls_disj_survives {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {old new : List Ivl} {log : Nat}
    (hAs : ArenaOK s) (hAp : ArenaOK post) (hl : LogEntryOK s log)
    (hu : IvlUnhit s post (log, 40))
    (hsys : globN post "vm_system_address" = globN s "vm_system_address")
    (hog : OwnedGrows s post old new) (hd : IvlsDisj (logOwnedIvls s log) old) :
    IvlsDisj (logOwnedIvls post log) new := by
  rw [logOwnedIvls_eq_of_unhit hAs hl hu hsys]
  intro o ho
  have hmem := (List.mem_filter.mp ho).1
  exact allocated_disj_ownedGrows hAs hAp
    (Or.inl (logEntryOK_record_placed hl o hmem)) hog (hd o ho)

/-- Reassemble the log-list invariant from preservation of the header, live
pointer cells and individual log records. This isolates the memory obligations
of the two ether-creation calls from the list invariant itself. -/
theorem logsListOK_congr_live {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {logs : Nat} (hAs : ArenaOK s) (hgS : GuestInv s) (hgP : GuestInv post)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (h : LogsListOK s logs)
    (halloc : Allocated s (logs, 24) → Allocated post (logs, 24))
    (hhead : ∀ k ∈ ([0, 8, 16] : List Nat),
      memW post (logs + k) = memW s (logs + k))
    (hptr : ∀ i, i < memW s (logs + 8) →
      memW post (memW s logs + 8 * i) = memW s (memW s logs + 8 * i))
    (hentry : ∀ i, i < memW s (logs + 8) →
      IvlUnhit s post (memW s (memW s logs + 8 * i), 40)) :
    LogsListOK post logs := by
  rcases h with hz | ⟨hw, ha, hn, hc, he⟩
  · exact Or.inl hz
  have h0 : memW post logs = memW s logs := by simpa using hhead 0 (by simp)
  have h8 := hhead 8 (by simp)
  have h16 := hhead 16 (by simp)
  refine Or.inr ⟨R13Shards.wordsOK_transfer hgS hgP hw, halloc ha, ?_, ?_, ?_⟩
  · rw [h8]; exact hn
  · rw [h8, h16]; exact hc
  · intro i hi
    rw [h8] at hi
    rw [h0, hptr i hi]
    exact ⟨R13Shards.wordAt_transfer hgS hgP (he i hi).1,
      R13Shards.logEntryOK_congr_unhit hAs hgS hgP hhp (he i hi).2 (hentry i hi)⟩

theorem logsListOK_congr_header_unhit {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {logs : Nat}
    (hAs : ArenaOK s) (hgS : GuestInv s) (hgP : GuestInv post)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (h : LogsListOK s logs)
    (halloc : Allocated s (logs, 24) → Allocated post (logs, 24))
    (hhead : IvlUnhit s post (logs, 24))
    (hptr : ∀ i, i < memW s (logs + 8) →
      memW post (memW s logs + 8 * i) = memW s (memW s logs + 8 * i))
    (hentry : ∀ i, i < memW s (logs + 8) →
      IvlUnhit s post (memW s (memW s logs + 8 * i), 40)) :
    LogsListOK post logs := by
  rcases h with hz | hl
  · exact Or.inl hz
  apply logsListOK_congr_live hAs hgS hgP hhp (Or.inr hl) halloc _ hptr hentry
  intro k hk
  have h8 := hl.1.1
  have hb := (R13Shards.ivl_allocated_bound hAs hl.2.1).2
  apply R13Shards.memW_eq_of_ivlUnhit hhead
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl <;> omega
  · exact hb
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl <;> (constructor <;> omega)

/-- The alternate scratch branch in the R11 ownership predicate is empty:
a 24-byte header cannot start at or above `scratchEnd` and end below it. -/
theorem logsOwnedDisj_header_heap {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {logs : Nat} (h : LogsOwnedDisj s S Nd logs) (hn : logs ≠ 0) :
    Inside (logs, 24) sourceBase (globN s "heap_ptr") := by
  rcases (h hn).1 with hh | ⟨hs, he⟩
  · exact hh
  · unfold Inside at hs
    simp only [he] at hs
    omega

/-- The log header is protected by the world-step frame once its scratch-write
disjointness is established. It remains disjoint from the new owned world. -/
theorem logsOwnedDisj_header_survives {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {logs : Nat}
    {new R : List Ivl} (hAs : ArenaOK s)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hlogs : LogsListOK s logs) (hd : LogsOwnedDisj s S Nd logs) (hn : logs ≠ 0)
    (hold0 : ∀ j ∈ worldOwned s S Nd, j.2 = 0 → j.1 % 8 = 0)
    (hR0 : ∀ j ∈ R, j.2 = 0 → j.1 % 8 = 0)
    (hog : OwnedGrows s post (worldOwned s S Nd) new)
    (hfr : FrameOutside s post (worldOwned s S Nd ++ R ++ [freeGap s]) (heapFree s))
    (hR : ∀ j ∈ R, Disj (logs, 24) j) :
    Inside (logs, 24) sourceBase (globN post "heap_ptr") ∧
    (∀ o ∈ new, Disj (logs, 24) o) ∧ IvlUnhit s post (logs, 24) := by
  rcases hlogs with hz | hl
  · exact False.elim (hn hz)
  exact R13Shards.heap_ivl_survives_step hAs hhp hold0 hR0 hog hfr
    hl.1.1 (by norm_num) (logsOwnedDisj_header_heap hd hn)
    (fun j hj => (hd hn).2.1 _ (by simp) j hj) hR

theorem logsOwnedDisj_entry_survives {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {logs i : Nat}
    {new R : List Ivl} (hAs : ArenaOK s)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hlogs : LogsListOK s logs) (hd : LogsOwnedDisj s S Nd logs) (hn : logs ≠ 0)
    (hi : i < memW s (logs + 8))
    (hold0 : ∀ j ∈ worldOwned s S Nd, j.2 = 0 → j.1 % 8 = 0)
    (hR0 : ∀ j ∈ R, j.2 = 0 → j.1 % 8 = 0)
    (hog : OwnedGrows s post (worldOwned s S Nd) new)
    (hfr : FrameOutside s post (worldOwned s S Nd ++ R ++ [freeGap s]) (heapFree s))
    (hR : ∀ j ∈ R, Disj (memW s (memW s logs + 8 * i), 40) j) :
    Inside (memW s (memW s logs + 8 * i), 40) sourceBase (globN post "heap_ptr") ∧
    (∀ o ∈ new, Disj (memW s (memW s logs + 8 * i), 40) o) ∧
    IvlUnhit s post (memW s (memW s logs + 8 * i), 40) := by
  rcases hlogs with hz | hl
  · exact False.elim (hn hz)
  have he := (hl.2.2.2.2 i hi).2
  exact R13Shards.heap_ivl_survives_step hAs hhp hold0 hR0 hog hfr
    he.1.1 (by norm_num) he.2.1
    (fun j hj => (hd hn).2.2 i hi _ (by simp) j hj) hR

/-- Live pointer-array preservation additionally needs its heap placement.
`LogsOwnedDisj` itself specifies disjointness but not placement of this array. -/
theorem logsOwnedDisj_array_survives {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {logs : Nat}
    {new R : List Ivl} (hAs : ArenaOK s)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hd : LogsOwnedDisj s S Nd logs) (hn : logs ≠ 0)
    (halign : memW s logs % 8 = 0)
    (hin : Inside (memW s logs, 8 * memW s (logs + 8)) sourceBase (globN s "heap_ptr"))
    (hold0 : ∀ j ∈ worldOwned s S Nd, j.2 = 0 → j.1 % 8 = 0)
    (hR0 : ∀ j ∈ R, j.2 = 0 → j.1 % 8 = 0)
    (hog : OwnedGrows s post (worldOwned s S Nd) new)
    (hfr : FrameOutside s post (worldOwned s S Nd ++ R ++ [freeGap s]) (heapFree s))
    (hR : ∀ j ∈ R, Disj (memW s logs, 8 * memW s (logs + 8)) j) :
    (∀ i, i < memW s (logs + 8) →
      memW post (memW s logs + 8 * i) = memW s (memW s logs + 8 * i)) ∧
    (∀ o ∈ new, Disj (memW s logs, 8 * memW s (logs + 8)) o) := by
  have hs := R13Shards.heap_ivl_survives_step hAs hhp hold0 hR0 hog hfr
    halign (by simp) hin (fun j hj => (hd hn).2.1 _ (by simp) j hj) hR
  refine ⟨?_, hs.2.1⟩
  intro i hi
  apply R13Shards.memW_eq_of_ivlUnhit hs.2.2
  · omega
  · exact (R13Shards.ivl_allocated_bound hAs (Or.inl hin)).2
  · constructor <;> dsimp <;> omega

/-- A nonempty log list does provide alignment of its backing pointer, through
the ordinary-domain membership of its first live cell. This does not bound
that cell by the current allocation frontier. -/
theorem logsListOK_array_aligned {F : Type} {s : PanSemStateFiniteExact 64 F}
    {logs : Nat} (hg : GuestInv s) (h : LogsListOK s logs) (hn : logs ≠ 0)
    (hlen : 0 < memW s (logs + 8)) : memW s logs % 8 = 0 := by
  rcases h with hz | hl
  · exact False.elim (hn hz)
  obtain ⟨w, hdom, _⟩ := (hl.2.2.2.2 0 hlen).1
  rw [hg.memaddrs] at hdom
  have ha := (R13Shards.ordinaryDomain_iff _).mp hdom
  have hlt : memW s logs < 2 ^ 64 := by
    unfold memW
    cases s.memory (BitVec.ofNat 64 logs) with
    | word v => exact v.isLt
  simpa only [Nat.mul_zero, Nat.add_zero, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] using ha.1

/-- A framed world step preserves the entire log list when its live array is
heap-resident and all live log storage avoids the explicit write footprint. -/
theorem logsListOK_of_framed_step {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {logs : Nat}
    {new R : List Ivl} (hAs : ArenaOK s) (hgS : GuestInv s) (hgP : GuestInv post)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hlogs : LogsListOK s logs) (hd : LogsOwnedDisj s S Nd logs)
    (harray : logs ≠ 0 → memW s logs % 8 = 0 ∧
      Inside (memW s logs, 8 * memW s (logs + 8)) sourceBase (globN s "heap_ptr"))
    (hold0 : ∀ j ∈ worldOwned s S Nd, j.2 = 0 → j.1 % 8 = 0)
    (hR0 : ∀ j ∈ R, j.2 = 0 → j.1 % 8 = 0)
    (hog : OwnedGrows s post (worldOwned s S Nd) new)
    (hfr : FrameOutside s post (worldOwned s S Nd ++ R ++ [freeGap s]) (heapFree s))
    (hRh : ∀ j ∈ R, Disj (logs, 24) j)
    (hRa : ∀ j ∈ R, Disj (memW s logs, 8 * memW s (logs + 8)) j)
    (hRe : ∀ i, i < memW s (logs + 8) →
      ∀ j ∈ R, Disj (memW s (memW s logs + 8 * i), 40) j) :
    LogsListOK post logs := by
  by_cases hn : logs = 0
  · exact Or.inl hn
  have hh := logsOwnedDisj_header_survives hAs hhp hlogs hd hn hold0 hR0 hog hfr hRh
  have ha := logsOwnedDisj_array_survives hAs hhp hd hn
    (harray hn).1 (harray hn).2 hold0 hR0 hog hfr hRa
  apply logsListOK_congr_header_unhit hAs hgS hgP hhp hlogs
    (fun _ => Or.inl hh.1) hh.2.2 ha.1
  intro i hi
  exact (logsOwnedDisj_entry_survives hAs hhp hlogs hd hn hi
    hold0 hR0 hog hfr (hRe i hi)).2.2

/-- Empty arrays need no placement premise. For nonempty arrays, alignment
follows from `LogsListOK`, leaving only heap placement as an extra obligation. -/
theorem logsListOK_of_framed_step_live {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {logs : Nat}
    {new R : List Ivl} (hAs : ArenaOK s) (hgS : GuestInv s) (hgP : GuestInv post)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hlogs : LogsListOK s logs) (hd : LogsOwnedDisj s S Nd logs)
    (harray : logs ≠ 0 → 0 < memW s (logs + 8) →
      Inside (memW s logs, 8 * memW s (logs + 8)) sourceBase (globN s "heap_ptr"))
    (hold0 : ∀ j ∈ worldOwned s S Nd, j.2 = 0 → j.1 % 8 = 0)
    (hR0 : ∀ j ∈ R, j.2 = 0 → j.1 % 8 = 0)
    (hog : OwnedGrows s post (worldOwned s S Nd) new)
    (hfr : FrameOutside s post (worldOwned s S Nd ++ R ++ [freeGap s]) (heapFree s))
    (hRh : ∀ j ∈ R, Disj (logs, 24) j)
    (hRa : ∀ j ∈ R, Disj (memW s logs, 8 * memW s (logs + 8)) j)
    (hRe : ∀ i, i < memW s (logs + 8) →
      ∀ j ∈ R, Disj (memW s (memW s logs + 8 * i), 40) j) :
    LogsListOK post logs := by
  by_cases hn : logs = 0
  · exact Or.inl hn
  have hh := logsOwnedDisj_header_survives hAs hhp hlogs hd hn hold0 hR0 hog hfr hRh
  apply logsListOK_congr_header_unhit hAs hgS hgP hhp hlogs
    (fun _ => Or.inl hh.1) hh.2.2
  · intro i hi
    have hpos : 0 < memW s (logs + 8) := by omega
    exact (logsOwnedDisj_array_survives hAs hhp hd hn
      (logsListOK_array_aligned hgS hlogs hn hpos) (harray hn hpos)
      hold0 hR0 hog hfr hRa).1 i hi
  · intro i hi
    exact (logsOwnedDisj_entry_survives hAs hhp hlogs hd hn hi
      hold0 hR0 hog hfr (hRe i hi)).2.2

/-- Live arrays retain both their pointer cells and their separation from the
new world. Empty arrays need no alignment, even when their pointer is arbitrary. -/
theorem logsLiveOwned_array_survives {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {logs : Nat}
    {new R : List Ivl} (hAs : ArenaOK s) (hAp : ArenaOK post)
    (hgS : GuestInv s) (hgrow : AllocatorGrows s post)
    (hl : LogsListOK s logs) (hd : LogsLiveOwned s S Nd logs) (hn : logs ≠ 0)
    (hold0 : ∀ j ∈ worldOwned s S Nd, j.2 = 0 → j.1 % 8 = 0)
    (hR0 : ∀ j ∈ R, j.2 = 0 → j.1 % 8 = 0)
    (hog : OwnedGrows s post (worldOwned s S Nd) new)
    (hfr : FrameOutside s post (worldOwned s S Nd ++ R ++ [freeGap s]) (heapFree s))
    (hRa : ∀ j ∈ R, Disj (memW s logs, 8 * memW s (logs + 8)) j) :
    Allocated post (memW s logs, 8 * memW s (logs + 8)) ∧
    (∀ o ∈ new, Disj (memW s logs, 8 * memW s (logs + 8)) o) ∧
    (∀ i, i < memW s (logs + 8) →
      memW post (memW s logs + 8 * i) = memW s (memW s logs + 8 * i)) := by
  refine ⟨hgrow.allocated (hd hn).1, ?_⟩
  by_cases hz : memW s (logs + 8) = 0
  · constructor
    · intro o ho
      exact Or.inl (by simp [hz])
    · intro i hi
      omega
  have hp : 0 < memW s (logs + 8) := by omega
  have ha := allocated_ivl_survives_step hAs hAp hgrow hold0 hR0 hog hfr
    (logsListOK_array_aligned hgS hl hn hp) (by simp)
    (hd hn).1 (fun j hj => (hd hn).2.1 _ (by simp) j hj) hRa
  refine ⟨ha.2.1, ?_⟩
  intro i hi
  apply R13Shards.memW_eq_of_ivlUnhit ha.2.2
  · have := logsListOK_array_aligned hgS hl hn hp; omega
  · exact (R13Shards.ivl_allocated_bound hAs (hd hn).1).2
  · constructor <;> dsimp <;> omega

/-- Preservation for the actual temporary lists returned by the guest: both
heap and live scratch headers/arrays are allowed, and empty arrays are ignored. -/
theorem logsLiveOwned_list_survives {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {logs : Nat}
    {new R : List Ivl} (hAs : ArenaOK s) (hAp : ArenaOK post)
    (hgS : GuestInv s) (hgP : GuestInv post) (hgrow : AllocatorGrows s post)
    (hl : LogsListOK s logs) (hd : LogsLiveOwned s S Nd logs)
    (hold0 : ∀ j ∈ worldOwned s S Nd, j.2 = 0 → j.1 % 8 = 0)
    (hR0 : ∀ j ∈ R, j.2 = 0 → j.1 % 8 = 0)
    (hog : OwnedGrows s post (worldOwned s S Nd) new)
    (hfr : FrameOutside s post (worldOwned s S Nd ++ R ++ [freeGap s]) (heapFree s))
    (hRh : ∀ j ∈ R, Disj (logs, 24) j)
    (hRa : ∀ j ∈ R, Disj (memW s logs, 8 * memW s (logs + 8)) j)
    (hRe : ∀ i, i < memW s (logs + 8) →
      ∀ j ∈ R, Disj (memW s (memW s logs + 8 * i), 40) j) :
    LogsListOK post logs := by
  by_cases hn : logs = 0
  · exact Or.inl hn
  have hl' := hl.resolve_left hn
  have hh := allocated_ivl_survives_step hAs hAp hgrow hold0 hR0 hog hfr
    hl'.1.1 (by norm_num : 24 % 8 = 0) hl'.2.1
    (fun j hj => (hd hn).2.1 _ (by simp) j hj) hRh
  apply logsListOK_congr_header_unhit hAs hgS hgP hgrow.1 hl
    (fun _ => hh.1) hh.2.2
  · intro i hi
    exact (logsLiveOwned_array_survives hAs hAp hgS hgrow hl hd hn
      hold0 hR0 hog hfr hRa).2.2 i hi
  · intro i hi
    have he := (hl'.2.2.2.2 i hi).2
    have hmem : (memW s (memW s logs + 8 * i), 40) ∈
        logOwnedIvls s (memW s (memW s logs + 8 * i)) := by
      simp [logOwnedIvls, logRecordIvls]
    exact (R13Shards.heap_ivl_survives_step hAs hgrow.1 hold0 hR0 hog hfr
      he.1.1 (by norm_num) he.2.1
      (fun j hj => (hd hn).2.2 i hi _ hmem j hj) (hRe i hi)).2.2

/-- Full ownership transport, so the same invariant can be used again for the
second ether-creation call and then for receipt encoding. -/
theorem logsLiveOwned_survives {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd S' Nd' : List Nat} {logs : Nat}
    {R : List Ivl} (hAs : ArenaOK s) (hAp : ArenaOK post)
    (hgS : GuestInv s) (hgrow : AllocatorGrows s post)
    (hl : LogsListOK s logs) (hd : LogsLiveOwned s S Nd logs)
    (hsys : globN post "vm_system_address" = globN s "vm_system_address")
    (hold0 : ∀ j ∈ worldOwned s S Nd, j.2 = 0 → j.1 % 8 = 0)
    (hR0 : ∀ j ∈ R, j.2 = 0 → j.1 % 8 = 0)
    (hog : OwnedGrows s post (worldOwned s S Nd) (worldOwned post S' Nd'))
    (hfr : FrameOutside s post (worldOwned s S Nd ++ R ++ [freeGap s]) (heapFree s))
    (hRh : ∀ j ∈ R, Disj (logs, 24) j)
    (hRa : ∀ j ∈ R, Disj (memW s logs, 8 * memW s (logs + 8)) j)
    (hRe : ∀ i, i < memW s (logs + 8) →
      ∀ j ∈ R, Disj (memW s (memW s logs + 8 * i), 40) j) :
    LogsLiveOwned post S' Nd' logs := by
  intro hn
  have hl' := hl.resolve_left hn
  have hh := allocated_ivl_survives_step hAs hAp hgrow hold0 hR0 hog hfr
    hl'.1.1 (by norm_num : 24 % 8 = 0) hl'.2.1
    (fun j hj => (hd hn).2.1 _ (by simp) j hj) hRh
  have ha := logsLiveOwned_array_survives hAs hAp hgS hgrow hl hd hn
    hold0 hR0 hog hfr hRa
  have hb := (R13Shards.ivl_allocated_bound hAs hl'.2.1).2
  have h0 : memW post logs = memW s logs :=
    R13Shards.memW_eq_of_ivlUnhit hh.2.2 hl'.1.1 hb ⟨by omega, by omega⟩
  have h8 : memW post (logs + 8) = memW s (logs + 8) :=
    R13Shards.memW_eq_of_ivlUnhit hh.2.2 (by have := hl'.1.1; omega) hb
      ⟨by omega, by omega⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [h0, h8]; exact ha.1
  · intro o ho j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · exact hh.2.1 j hj
    · rw [h0, h8]; exact ha.2.1 j hj
  · intro i hi
    rw [h8] at hi
    rw [h0, ha.2.2 i hi]
    have he := (hl'.2.2.2.2 i hi).2
    have hmem : (memW s (memW s logs + 8 * i), 40) ∈
        logOwnedIvls s (memW s (memW s logs + 8 * i)) := by
      simp [logOwnedIvls, logRecordIvls]
    have hu := (R13Shards.heap_ivl_survives_step hAs hgrow.1 hold0 hR0 hog hfr
      he.1.1 (by norm_num) he.2.1
      (fun j hj => (hd hn).2.2 i hi _ hmem j hj) (hRe i hi)).2.2
    exact logOwnedIvls_disj_survives hAs hAp he hu hsys hog ((hd hn).2.2 i hi)

/-- Discharge all explicit scratch-buffer obligations for live logs at once.
This applies to the account mutation footprint, including the 52-byte sk buffer. -/
theorem logsLiveOwned_scratchStep {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd S' Nd' : List Nat} {logs : Nat}
    {gs : List (String × Nat × Nat)} (hgs : ScratchSpec gs)
    (hAs : ArenaOK s) (hAp : ArenaOK post) (hgS : GuestInv s) (hgP : GuestInv post)
    (hW : WorldTypedWith s S Nd) (hgrow : AllocatorGrows s post)
    (hl : LogsListOK s logs) (hd : LogsLiveOwned s S Nd logs)
    (hsys : globN post "vm_system_address" = globN s "vm_system_address")
    (hog : OwnedGrows s post (worldOwned s S Nd) (worldOwned post S' Nd'))
    (hfr : FrameOutside s post
      (worldOwned s S Nd ++ gs.map (fun e => bufferRegion s (e.1, e.2.2)) ++ [freeGap s])
      (heapFree s)) :
    LogsListOK post logs ∧ LogsLiveOwned post S' Nd' logs := by
  by_cases hn : logs = 0
  · exact ⟨Or.inl hn, fun h => False.elim (h hn)⟩
  have hR0 : ∀ j ∈ gs.map (fun e => bufferRegion s (e.1, e.2.2)),
      j.2 = 0 → j.1 % 8 = 0 := by
    intro j hj
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hj
    exact bufferRegion_zero_aligned s e.1 e.2.2 (by have := (hgs e he).2.2.1; omega)
  have hdisj : ∀ b : Ivl, (∀ j ∈ worldOwned s S Nd, Disj b j) →
      ∀ j ∈ gs.map (fun e => bufferRegion s (e.1, e.2.2)), Disj b j := by
    intro b hb j hj
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hj
    exact heap_ivl_disj_bufferRegion_le hb (e.1, e.2.1) (hgs e he).1
      e.2.2 (hgs e he).2.2.2
  have hh := hdisj (logs, 24) (fun j hj => (hd hn).2.1 _ (by simp) j hj)
  have ha := hdisj (memW s logs, 8 * memW s (logs + 8))
    (fun j hj => (hd hn).2.1 _ (by simp) j hj)
  have he : ∀ i, i < memW s (logs + 8) →
      ∀ j ∈ gs.map (fun e => bufferRegion s (e.1, e.2.2)),
        Disj (memW s (memW s logs + 8 * i), 40) j := by
    intro i hi
    apply hdisj
    intro j hj
    exact (hd hn).2.2 i hi _ (by simp [logOwnedIvls, logRecordIvls]) j hj
  exact ⟨logsLiveOwned_list_survives hAs hAp hgS hgP hgrow hl hd
      (R13Shards.worldOwned_zero_aligned hW) hR0 hog hfr hh ha he,
    logsLiveOwned_survives hAs hAp hgS hgrow hl hd hsys
      (R13Shards.worldOwned_zero_aligned hW) hR0 hog hfr hh ha he⟩

def etherScratchSpec : List (String × Nat × Nat) :=
  [("keccak_pad", 136, 136), ("keccak_st", 200, 200),
   ("mpt_nib_scratch", 64, 64), ("sk_buf", 64, 52)]

theorem etherScratchSpec_ok : ScratchSpec etherScratchSpec := by
  unfold ScratchSpec etherScratchSpec
  decide

/-- Specialize the concrete ether-creation step to an entry typing that owns
the temporary logs. Its exit typing retains both validity and ownership. -/
theorem create_ether_logs {F : Type} (s : PanSemStateFiniteExact 64 F)
    (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (hc : s.code = originalRuntimeCode)
    (hlk : lookupCodeHOLFinite s.code.lookup (ofString "create_ether") vs =
      some (body, callee, ret))
    (hW : WorldOK (callEntryStateHOLFinite s callee))
    (hnt : (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).1 ≠ some .timeOut)
    (hr : Resumes (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).1)
    (S Nd : List Nat) (logs : Nat)
    (hWT : WorldTypedWith (callEntryStateHOLFinite s callee) S Nd)
    (hlogs : LogsListOK (callEntryStateHOLFinite s callee) logs)
    (hown : LogsLiveOwned (callEntryStateHOLFinite s callee) S Nd logs) :
    let post := (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).2
    ∃ S' Nd', WorldTypedWith post S' Nd' ∧
      LogsListOK post logs ∧ LogsLiveOwned post S' Nd' logs := by
  let ent := callEntryStateHOLFinite s callee
  let post := (evaluateHOLFiniteState ent body).2
  have hw := funSpec_at_lookup EvmEkFk.wkSc_create_ether s hc vs body callee ret hlk hW hnt hr
  have hR : IvlsDisj (R16WkAcctWs.bufRegions EvmEkFk.acctMutBufs ent)
      (worldTypedIvls ent S Nd) := by
    change IvlsDisj (etherScratchSpec.map (fun e => bufferRegion ent (e.1, e.2.2))) _
    intro i hi j hj
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hi
    obtain ⟨hgb, hnu, _, hle⟩ := etherScratchSpec_ok e he
    exact bufferRegion_disj_le hWT (e.1, e.2.1) hgb hnu e.2.2 hle j hj
  obtain ⟨S', Nd', _, hWT', hog, hfr, _⟩ := hw.1.2.2.2.2 S Nd hWT hR
  have hsys : globN post "vm_system_address" = globN ent "vm_system_address" :=
    R16Shards.globN_eq_of_lookup (hw.1.2.2.1 (ofString "vm_system_address") (by decide))
  have hp := logsLiveOwned_scratchStep etherScratchSpec_ok hW.1.2 hw.1.1.2
    hW.1.1 hw.1.1.1 hWT ⟨hw.1.2.1, hw.2⟩ hlogs hown hsys hog hfr
  exact ⟨S', Nd', hWT', hp⟩

/-- Caller-facing form, usable at either Phase-4 ether call: restore caller
locals while retaining the same live-log pointer and its receipt guard. -/
theorem create_ether_logs_resume {F : Type} (s : PanSemStateFiniteExact 64 F)
    (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode)
    (hlk : lookupCodeHOLFinite s.code.lookup (ofString "create_ether") vs =
      some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post))
    (hW : WorldOK s) (S Nd : List Nat) (logs : Nat)
    (hWT : WorldTypedWith s S Nd) (hlogs : LogsListOK s logs)
    (hown : LogsLiveOwned s S Nd logs) :
    ∃ S' Nd', WorldTypedWith { post with locals := s.locals } S' Nd' ∧
      LogsListOK { post with locals := s.locals } logs ∧
      LogsLiveOwned { post with locals := s.locals } S' Nd' logs ∧
      LogsDisjFixed { post with locals := s.locals } logs := by
  have hWTc := (R13Shards.worldTypedWith_with_locals s callee (s.clock - 1) S Nd).mpr hWT
  have hLc := (R13Shards.logsListOK_with_locals s callee (s.clock - 1) logs).mpr hlogs
  have hp := create_ether_logs s vs body callee ret hc hlk
    (worldOK_callEntry hW callee) (by rw [hb]; simp)
    (by rw [hb]; exact Or.inl ⟨v, rfl⟩) S Nd logs hWTc hLc hown
  rw [hb] at hp
  obtain ⟨S', Nd', hWT', hL', hO'⟩ := hp
  have hOr : LogsLiveOwned { post with locals := s.locals } S' Nd' logs := hO'
  exact ⟨S', Nd',
    (R13Shards.worldTypedWith_with_locals post s.locals post.clock S' Nd').mpr hWT',
    (R13Shards.logsListOK_with_locals post s.locals post.clock logs).mpr hL',
    hOr, logsLiveOwned_disjFixed hOr⟩

/-- Changing only the caller locals transports the strong post-message cut. -/
theorem txAfterCallStrong_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat)
    (hi : locals.lookup (ofString "index") = s.locals.lookup (ofString "index"))
    (ho : locals.lookup (ofString "out") = s.locals.lookup (ofString "out"))
    (h : TxAfterCallStrong s) :
    TxAfterCallStrong { s with locals := locals, clock := k } := by
  have hout := locN_congr s locals k "out" ho
  obtain ⟨hW, hw, hin, hl, S, Nd, hWT, hd, hown⟩ := h
  refine ⟨⟨localsFree_worldOK s locals k hW.1,
    txEnv_with_locals s locals k hi hW.2⟩, ?_, ?_, ?_, S, Nd,
    (R13Shards.worldTypedWith_with_locals s locals k S Nd).mpr hWT, ?_, ?_⟩
  · change WordsOK s (locN { s with locals := locals, clock := k } "out", 96)
    rw [hout]; exact hw
  · change Inside (locN { s with locals := locals, clock := k } "out", 96)
      sourceBase (globN s "heap_ptr")
    rw [hout]; exact hin
  · rw [hout]
    exact (R13Shards.logsListOK_with_locals s locals k _).mpr hl
  · change IvlsDisj [(locN { s with locals := locals, clock := k } "out", 96)]
      (worldOwned s S Nd)
    rw [hout]; exact hd
  · change LogsLiveOwned s S Nd
      (memW s (locN { s with locals := locals, clock := k } "out" + 16))
    rw [hout]; exact hown

theorem localsOnly_txAfterCallStrong : LocalsOnly ["index", "out"] TxAfterCallStrong := by
  intro F s locals k hl h
  exact txAfterCallStrong_with_locals s locals k
    (hl "index" (by simp)) (hl "out" (by simp)) h

/-- A scratch-buffer world step preserves the complete output record and its
live logs under one common exit world typing. -/
theorem txAfterCallStrong_scratchStep {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)} {boKeep : List Nat}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {r : Option (PanSemResultExact 64)}
    (hstep : WorldStep R gw keep Q s r post) (h : TxAfterCallStrong s)
    (hgrow : AllocatorGrows s post)
    {gs : List (String × Nat × Nat)} (hgs : ScratchSpec gs)
    (hR : R s = gs.map (fun e => bufferRegion s (e.1, e.2.2)))
    (hbo : ofString "bo" ∉ gw.map ofString)
    (hjcap : ofString "journal_cap" ∉ gw.map ofString)
    (hsys : ofString "vm_system_address" ∉ gw.map ofString)
    (hkeep : ("bo", boKeep) ∈ keep)
    (hoffs : ∀ k ∈ ([24, 32, 40, 72, 80] : List Nat), k ∈ boKeep) :
    TxAfterCallStrong { post with locals := s.locals } := by
  obtain ⟨hW, hw, hin, hl, S, Nd, hWT, hd, hown⟩ := h
  have hRdisj : IvlsDisj (R s) (worldTypedIvls s S Nd) := by
    rw [hR]
    intro i hi j hj
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hi
    exact bufferRegion_disj_le hWT (e.1, e.2.1) (hgs e he).1
      (hgs e he).2.1 e.2.2 (hgs e he).2.2.2 j hj
  obtain ⟨S', Nd', _, hWT', hog, hfr, _⟩ := hstep.2.2.2.2 S Nd hWT hRdisj
  have hR0 : ∀ i ∈ R s, i.2 = 0 → i.1 % 8 = 0 := by
    rw [hR]
    intro i hi
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hi
    exact bufferRegion_zero_aligned s e.1 e.2.2
      (by have := (hgs e he).2.2.1; omega)
  have hRout : ∀ i ∈ R s, Disj (locN s "out", 96) i := by
    rw [hR]
    intro i hi
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hi
    exact heap_ivl_disj_bufferRegion_le (fun j hj => hd _ (by simp) j hj)
      (e.1, e.2.1) (hgs e he).1 e.2.2 (hgs e he).2.2.2
  obtain ⟨hin', hd', hu⟩ := R13Shards.heap_ivl_survives_step hW.1.1.2 hgrow.1
    (R13Shards.worldOwned_zero_aligned hWT) hR0 hog hfr hw.1 (by norm_num)
    hin (fun j hj => hd _ (by simp) j hj) hRout
  have hout16 : memW post (locN s "out" + 16) = memW s (locN s "out" + 16) :=
    memW_eq_of_ivlUnhit hu (by have := hw.1; omega)
      (ivl_allocated_bound hW.1.1.2 (Or.inl hin)).2 ⟨by omega, by omega⟩
  have hsysEq : globN post "vm_system_address" = globN s "vm_system_address" :=
    R16Shards.globN_eq_of_lookup (hstep.2.2.1 _ hsys)
  have hfr' : FrameOutside s post
      (worldOwned s S Nd ++ gs.map (fun e => bufferRegion s (e.1, e.2.2)) ++ [freeGap s])
      (heapFree s) := by simpa only [hR] using hfr
  have hlogs := logsLiveOwned_scratchStep hgs hW.1.1.2 hstep.1.2
    hW.1.1.1 hstep.1.1 hWT hgrow hl hown hsysEq hog hfr'
  have hRbo : ∀ i ∈ R s, Disj i (globN s "bo", 88) :=
    fun i hi => hRdisj i hi _ (bo_mem_typed hW.2.bo_nz)
  have hE := txEnv_preserved_by_worldStep hstep hbo hjcap hkeep hoffs hRbo
    (bo_words hWT.2.2.1 hW.2.bo_nz).2.1 hR0 hW.2 rfl
  refine ⟨⟨worldOK_of_parts
    ((arenaReady_with_locals post s.locals post.clock).mpr hstep.1)
    ((R13Shards.worldTypedWith_with_locals post s.locals post.clock S' Nd').mpr hWT'),
    hE⟩, ?_, hin', ?_, S', Nd',
    (R13Shards.worldTypedWith_with_locals post s.locals post.clock S' Nd').mpr hWT',
    ?_, ?_⟩
  · exact wordsOK_transfer hW.1.1.1 hstep.1.1 hw
  · change LogsListOK { post with locals := s.locals } (memW post (locN s "out" + 16))
    rw [hout16]
    exact (R13Shards.logsListOK_with_locals post s.locals post.clock _).mpr hlogs.1
  · intro i hi j hj
    simp only [List.mem_singleton] at hi
    subst i
    exact hd' j hj
  · change LogsLiveOwned post S' Nd' (memW post (locN s "out" + 16))
    rw [hout16]; exact hlogs.2

/-- Heap-only world steps preserve the output record and its live logs. -/
theorem txAfterCallStrong_heapStep {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {r : Option (PanSemResultExact 64)}
    (hs : WorldStep (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])] Q s r post)
    (h : TxAfterCallStrong s) : TxAfterCallStrong { post with locals := s.locals } := by
  have hsc : globN post "scratch_ptr" = globN s "scratch_ptr" :=
    R16Shards.globN_eq_of_lookup (hs.2.2.1 _ (by decide))
  exact txAfterCallStrong_scratchStep
    (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])
    hs h ⟨hs.2.1, by omega⟩ (gs := []) (by intro e he; cases he)
    rfl (by decide) (by decide) (by decide) (by simp)
    (by intro k hk; simp only [List.mem_cons, List.not_mem_nil, or_false] at hk ⊢
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> simp)

/-- Both ether credits retain the output record and its live logs. -/
theorem create_ether_txAfterCallStrong_resume {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "create_ether") vs =
      some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) (h : TxAfterCallStrong s) :
    TxAfterCallStrong { post with locals := s.locals } := by
  have hw := funSpec_at_lookup EvmEkFk.wkSc_create_ether s hc vs body callee ret hl
    (worldOK_callEntry h.1.1 callee) (by rw [hb]; simp)
  rw [hb] at hw
  have hs := hw (Or.inl ⟨v, rfl⟩)
  have hs' := R13Shards.worldStep_with_locals hs.1 s.locals s.clock
  exact txAfterCallStrong_scratchStep
    (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])
    hs' h ⟨hs.1.2.1, hs.2⟩ etherScratchSpec_ok
    rfl (by decide) (by decide) (by decide) (by simp)
    (by intro k hk; simp only [List.mem_cons, List.not_mem_nil, or_false] at hk ⊢
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> simp)

theorem lst_new_txAfterCallStrong_resume (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs =
      some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) (hp : TxAfterCallStrong s) :
    TxAfterCallStrong (setVarHOLFinite (ofString "logs") v
      { post with locals := s.locals }) := by
  have hw := funSpec_at_lookup h.wk_lst_new s hc vs body callee ret hl
    (worldOK_callEntry hp.1.1 callee) (by rw [hb]; simp)
  rw [hb] at hw
  have hs := hw (Or.inl ⟨v, rfl⟩)
  have hs' := R13Shards.worldStep_with_locals hs s.locals s.clock
  exact LocalsOnly.setVar localsOnly_txAfterCallStrong (by decide) v _
    (txAfterCallStrong_heapStep hs' hp)

theorem hoare_create_ether_txAfterCallStrong (args : List (ExpHOL 64)) :
    Hoare TxAfterCallStrong (.call (some (none, none)) (ofString "create_ether") args)
      (fun r t => r = none → TxAfterCallStrong t) := by
  apply R13Shards.Hoare.call0_resume
  intro F s vs body callee ret v post hc hp _ hl hb
  exact create_ether_txAfterCallStrong_resume s vs body callee ret v post hc hl hb hp

theorem resume_ro_txAfterCallStrong {fname name : MlS}
    (hro : ReadOnlyFn fname)
    (hne : ∀ k ∈ (["index", "out"] : List String), ofString k ≠ name)
    (args : List (ExpHOL 64)) :
    DecCallResumeOn TxAfterCallStrong TxAfterCallStrong name fname args := by
  intro F s vs body callee ret v post hc hp _ hl hb
  have hs := funSpec_at_lookup hro s hc vs body callee ret hl
    (guestInv_callEntry s callee hp.1.1.1.1) (by rw [hb]; simp)
  rw [hb] at hs
  have he := hs (Or.inl ⟨v, rfl⟩)
  dsimp only at he
  have he' : ({ post with locals := s.locals } : PanSemStateFiniteExact 64 F) =
      { s with clock := post.clock } := by rw [he]; rfl
  apply LocalsOnly.setVar localsOnly_txAfterCallStrong hne v
  rw [he']
  exact txAfterCallStrong_with_locals s s.locals post.clock rfl rfl hp

theorem txAfterCallStrong_guest_entry (fn : MlS) (args : List (ExpHOL 64)) :
    CallEntryOn TxAfterCallStrong GuestInv fn args := by
  intro F s vs body callee ret hc hp ha hl
  exact guestInv_callEntry s callee hp.1.1.1.1

/-- The refund arithmetic and both ether credits, before updating block totals. -/
def phase4CreditPrefix (tail : ProgHOL 64) : ProgHOL 64 :=
  spinePlug 11 (spineAt 99 ptxCode) tail

def phase4CreditCost : Nat :=
  (K.udiv_small5 + 1) + (K.min + 1) + (K.max + 1) +
  (K.fee_mul + 1) + (K.u256_sub + 1) + (K.fee_mul + 1) +
  (K.create_ether + 1) + (K.create_ether + 1)

theorem phase4CreditPrefix_cut (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn TxAfterCallStrong tail b) :
    TerminatingProgBoundedOn TxAfterCallStrong (phase4CreditPrefix tail)
      (phase4CreditCost + b) := by
  have hb : TerminatingProgBoundedOn TxAfterCallStrong (phase4CreditPrefix tail)
      (K.udiv_small5 + (K.min + (K.max + (K.fee_mul +
        (K.u256_sub + (K.fee_mul + ((K.create_ether + 1) +
          ((K.create_ether + 1) + b)) + 1) + 1) + 1) + 1) + 1) + 1) := by
    unfold phase4CreditPrefix ptxCode
    refine TerminatingProgBoundedOn.dec_onLocals localsOnly_txAfterCallStrong _ (by decide) _ _ ?_
    refine TerminatingProgBoundedOn.decCall_on h.fb_udiv_small5 _ _ _
      (txAfterCallStrong_guest_entry _ _)
      (resume_ro_txAfterCallStrong h.ro_udiv_small5 (by decide) _) ?_
    refine TerminatingProgBoundedOn.decCall_on h.fb_min _ _ _
      (txAfterCallStrong_guest_entry _ _)
      (resume_ro_txAfterCallStrong h.ro_min (by decide) _) ?_
    refine TerminatingProgBoundedOn.dec_onLocals localsOnly_txAfterCallStrong _ (by decide) _ _ ?_
    refine TerminatingProgBoundedOn.decCall_on h.fb_max _ _ _
      (txAfterCallStrong_guest_entry _ _)
      (resume_ro_txAfterCallStrong h.ro_max (by decide) _) ?_
    refine TerminatingProgBoundedOn.dec_onLocals localsOnly_txAfterCallStrong _ (by decide) _ _ ?_
    refine TerminatingProgBoundedOn.decCall_on h.fb_fee_mul _ _ _
      (txAfterCallStrong_guest_entry _ _)
      (resume_ro_txAfterCallStrong h.ro_fee_mul (by decide) _) ?_
    refine TerminatingProgBoundedOn.decCall_on h.fb_u256_sub _ _ _
      (txAfterCallStrong_guest_entry _ _)
      (resume_ro_txAfterCallStrong h.ro_u256_sub (by decide) _) ?_
    refine TerminatingProgBoundedOn.decCall_on h.fb_fee_mul _ _ _
      (txAfterCallStrong_guest_entry _ _)
      (resume_ro_txAfterCallStrong h.ro_fee_mul (by decide) _) ?_
    refine seq_bound_trans ?_ (hoare_create_ether_txAfterCallStrong _) ?_
    · exact bound_mono (TerminatingProgBoundedOn.call_guestInv h.fb_create_ether none _)
        (fun s hp => hp.1.1.1.1)
    refine seq_bound_trans ?_ (hoare_create_ether_txAfterCallStrong _) htail
    exact bound_mono (TerminatingProgBoundedOn.call_guestInv h.fb_create_ether none _)
      (fun s hp => hp.1.1.1.1)
  have he : K.udiv_small5 + (K.min + (K.max + (K.fee_mul +
        (K.u256_sub + (K.fee_mul + ((K.create_ether + 1) +
          ((K.create_ether + 1) + b)) + 1) + 1) + 1) + 1) + 1) + 1 =
      phase4CreditCost + b := by unfold phase4CreditCost; omega
  rw [he] at hb
  intro F s hc hp
  exact hb s hc hp

/-- A single write inside world storage cannot change an owned live log list. -/
theorem logsLiveOwned_single_store {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {logs : Nat} {x : BitVec 64}
    {mem' : BitVec 64 → HolWordLab 64}
    (hA : ArenaOK s) (hg : GuestInv s) (hgp : GuestInv {s with memory := mem'})
    (hl : LogsListOK s logs) (hd : LogsLiveOwned s S Nd logs)
    (hm : ∀ a, a ≠ x → mem' a = s.memory a)
    (hwrite : ∃ o ∈ worldOwned s S Nd, Inside (x.toNat, 8) o.1 (o.1 + o.2))
    (howned : worldOwned {s with memory := mem'} S Nd = worldOwned s S Nd) :
    LogsListOK {s with memory := mem'} logs ∧
      LogsLiveOwned {s with memory := mem'} S Nd logs := by
  let post := {s with memory := mem'}
  by_cases hn : logs = 0
  · exact ⟨Or.inl hn, fun h => False.elim (h hn)⟩
  have hl' := hl.resolve_left hn
  obtain ⟨o, ho, hin⟩ := hwrite
  have hdisj : ∀ b, (∀ j ∈ worldOwned s S Nd, Disj b j) → Disj b (x.toNat, 8) :=
    fun b hb => disj_of_inside_right hin (hb o ho)
  have hh : IvlUnhit s post (logs, 24) :=
    ivlUnhit_single hm (by simp) (hdisj _ (fun j hj => (hd hn).2.1 _ (by simp) j hj))
  have hb := (ivl_allocated_bound hA hl'.2.1).2
  have h0 : memW post logs = memW s logs :=
    memW_eq_of_ivlUnhit hh hl'.1.1 hb ⟨by omega, by omega⟩
  have h8 : memW post (logs + 8) = memW s (logs + 8) :=
    memW_eq_of_ivlUnhit hh (by have := hl'.1.1; omega) hb ⟨by omega, by omega⟩
  have hp : ∀ i, i < memW s (logs + 8) →
      memW post (memW s logs + 8 * i) = memW s (memW s logs + 8 * i) := by
    intro i hi
    have ha := logsListOK_array_aligned hg hl hn (by omega)
    have hu : IvlUnhit s post (memW s logs, 8 * memW s (logs + 8)) :=
      ivlUnhit_single hm (fun _ => ha)
        (hdisj _ (fun j hj => (hd hn).2.1 _ (by simp) j hj))
    exact memW_eq_of_ivlUnhit hu (by omega)
      (ivl_allocated_bound hA (hd hn).1).2 ⟨by dsimp; omega, by dsimp; omega⟩
  have he : ∀ i, i < memW s (logs + 8) →
      IvlUnhit s post (memW s (memW s logs + 8 * i), 40) := by
    intro i hi
    exact ivlUnhit_single hm (by simp)
      (hdisj _ (fun j hj => (hd hn).2.2 i hi _ (by simp [logOwnedIvls, logRecordIvls]) j hj))
  refine ⟨logsListOK_congr_header_unhit hA hg hgp (by rfl) hl
    (fun h => h) hh hp he, ?_⟩
  intro _
  change Allocated post (memW post logs, 8 * memW post (logs + 8)) ∧ _
  rw [h0, h8]
  refine ⟨(hd hn).1, ?_, ?_⟩
  · change IvlsDisj _ (worldOwned post S Nd)
    rw [howned]
    exact (hd hn).2.1
  · intro i hi
    rw [hp i hi]
    rw [logOwnedIvls_eq_of_unhit hA (hl'.2.2.2.2 i hi).2 (he i hi) rfl]
    change IvlsDisj _ (worldOwned post S Nd)
    rw [howned]
    exact (hd hn).2.2 i hi

/-- The four block-total cells are untyped and disjoint from the output/logs. -/
theorem txAfterCallStrong_store_bo {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : TxAfterCallStrong s) {off : Nat} (hoff : off ∈ ([0, 8, 16, 48] : List Nat))
    {x : BitVec 64} (hx : s.memaddrs x) (hxe : x.toNat = globN s "bo" + off)
    {mem' : BitVec 64 → HolWordLab 64} (hm : ∀ a, a ≠ x → mem' a = s.memory a) :
    TxAfterCallStrong {s with memory := mem'} := by
  obtain ⟨hW, hw, hin, hl, S, Nd, hWT, hd, hown⟩ := h
  let post := {s with memory := mem'}
  have hg : GuestInv post := guestInv_congr (s := s) rfl rfl rfl rfl hW.1.1.1
  obtain ⟨hWT', howned, hE⟩ := store_bo_untyped_world hW.1.1 hW.2 hWT hoff hx hxe hm
  have hbo : (globN s "bo", 88) ∈ worldOwned s S Nd :=
    R13Shards.worldTypedIvls_sub_worldOwned (bo_mem_typed hW.2.bo_nz)
  have hix : Inside (x.toNat, 8) (globN s "bo") (globN s "bo" + 88) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
    unfold Inside
    dsimp
    rcases hoff with rfl | rfl | rfl | rfl <;> omega
  have hu : IvlUnhit s post (locN s "out", 96) :=
    ivlUnhit_single hm (by simp)
      (disj_of_inside_right hix (hd _ (by simp) _ hbo))
  have h16 : memW post (locN s "out" + 16) = memW s (locN s "out" + 16) :=
    memW_eq_of_ivlUnhit hu (by have := hw.1; omega)
      (ivl_allocated_bound hW.1.1.2 (Or.inl hin)).2 ⟨by omega, by omega⟩
  have hlogs := logsLiveOwned_single_store hW.1.1.2 hW.1.1.1 hg hl hown hm
    ⟨_, hbo, hix⟩ howned
  refine ⟨⟨worldOK_of_parts ⟨hg, hW.1.1.2⟩ hWT', hE⟩,
    wordsOK_transfer hW.1.1.1 hg hw, hin, ?_, S, Nd, hWT', ?_, ?_⟩
  · change LogsListOK post (memW post (locN s "out" + 16))
    rw [h16]; exact hlogs.1
  · change IvlsDisj _ (worldOwned post S Nd)
    rw [howned]; exact hd
  · change LogsLiveOwned post S Nd (memW post (locN s "out" + 16))
    rw [h16]; exact hlogs.2

/-- An owned-world write that preserves world typing also preserves the output. -/
theorem txAfterCallStrong_worldStore {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : TxAfterCallStrong s) {x : BitVec 64}
    {mem' : BitVec 64 → HolWordLab 64} (hm : ∀ a, a ≠ x → mem' a = s.memory a)
    (hpres : ∀ S Nd, WorldTypedWith s S Nd →
      WorldTypedWith {s with memory := mem'} S Nd ∧
      worldOwned {s with memory := mem'} S Nd = worldOwned s S Nd ∧
      TxEnv {s with memory := mem'})
    (hx : ∀ S Nd, WorldTypedWith s S Nd →
      ∃ i ∈ worldOwned s S Nd, Inside (x.toNat, 8) i.1 (i.1 + i.2)) :
    TxAfterCallStrong {s with memory := mem'} := by
  obtain ⟨hW, hw, hin, hl, S, Nd, hWT, hd, hown⟩ := h
  let post := {s with memory := mem'}
  have hg : GuestInv post := guestInv_congr (s := s) rfl rfl rfl rfl hW.1.1.1
  obtain ⟨hWT', howned, hE⟩ := hpres S Nd hWT
  obtain ⟨i, hi, hix⟩ := hx S Nd hWT
  have hu : IvlUnhit s post (locN s "out", 96) :=
    ivlUnhit_single hm (by simp)
      (disj_of_inside_right hix (hd _ (by simp) _ hi))
  have h16 : memW post (locN s "out" + 16) = memW s (locN s "out" + 16) :=
    memW_eq_of_ivlUnhit hu (by have := hw.1; omega)
      (ivl_allocated_bound hW.1.1.2 (Or.inl hin)).2 ⟨by omega, by omega⟩
  have hlogs := logsLiveOwned_single_store hW.1.1.2 hW.1.1.1 hg hl hown hm
    ⟨i, hi, hix⟩ howned
  refine ⟨⟨worldOK_of_parts ⟨hg, hW.1.1.2⟩ hWT', hE⟩,
    wordsOK_transfer hW.1.1.1 hg hw, hin, ?_, S, Nd, hWT', ?_, ?_⟩
  · change LogsListOK post (memW post (locN s "out" + 16))
    rw [h16]; exact hlogs.1
  · change IvlsDisj _ (worldOwned post S Nd)
    rw [howned]; exact hd
  · change LogsLiveOwned post S Nd (memW post (locN s "out" + 16))
    rw [h16]; exact hlogs.2

theorem txAfterCallStrong_store_receipt {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : TxAfterCallStrong s) {x : BitVec 64} (hx : s.memaddrs x)
    (hin : Inside (x.toNat, 8) (memW s (globN s "bo" + 32))
      (memW s (globN s "bo" + 32) + (16 * memW s (globN s "bo" + 80) + 16)))
    {mem' : BitVec 64 → HolWordLab 64} (hm : ∀ a, a ≠ x → mem' a = s.memory a) :
    TxAfterCallStrong {s with memory := mem'} := by
  apply txAfterCallStrong_worldStore h hm
  · intro S Nd hWT
    exact store_bo_array_world h.1.1.1 h.1.2 hWT (Or.inl ⟨rfl, rfl⟩) hx hin hm
  · intro S Nd hWT
    obtain ⟨_, _, hbo⟩ := blockOutObjects_eq_list h.1.2 hWT.1
    refine ⟨(memW s (globN s "bo" + 32), 16 * memW s (globN s "bo" + 80) + 16), ?_, hin⟩
    have hmemb : (memW s (globN s "bo" + 32), 16 * memW s (globN s "bo" + 80) + 16)
        ∈ blockOutObjects s := by rw [hbo]; simp
    have hmemf : (memW s (globN s "bo" + 32), 16 * memW s (globN s "bo" + 80) + 16)
        ∈ fixedObjects s := List.mem_append_left _ (List.mem_append_right _ hmemb)
    unfold worldOwned
    simp only [List.mem_append]
    exact Or.inl (Or.inr hmemf)

theorem eval_add_global_const {F : Type} {s : PanSemStateFiniteExact 64 F}
    {g : String} {k x : BitVec 64}
    (hx : evalAt s (.op .add [.var .global (ofString g), .const k]) = some (.val (.word x))) :
    x.toNat = (globN s g + k.toNat) % 2 ^ 64 := by
  simp only [evalAt, evalHOLExact, evalListHOLExact] at hx
  rcases hg : s.globals.lookup (ofString g) with _ | vg
  · simp [hg] at hx
  · rcases vg with wg | _ | _
    · cases wg with
      | word gw =>
        simp only [hg, valueIsWord, valueWord, wordOpHOL, wordOp, List.all, List.map,
          Option.map, Bool.and_self, ↓reduceIte, List.foldr, Option.some.injEq,
          ValueHOL.val.injEq, HolWordLab.word.injEq] at hx
        have hgn : globN s g = gw.toNat := by simp [globN, hg]
        have hx' : x = gw + (k + 0) := hx.symm
        have hz0 : (0 : BitVec 64).toNat = 0 := by decide
        rw [hx', BitVec.toNat_add, BitVec.toNat_add, hz0, Nat.add_zero, Nat.add_mod_mod, hgn]
    · simp [hg, valueIsWord] at hx
    · simp [hg, valueIsWord] at hx

theorem hoare_store_bo_total (off : Nat) (hoff : off ∈ ([0, 8, 16, 48] : List Nat))
    (op : BinOp) (args : List (ExpHOL 64)) :
    Hoare TxAfterCallStrong
      (.store (.op .add [.var .global (ofString "bo"), .const (BitVec.ofNat 64 off)])
        (.op op args)) (fun r t => r = none → TxAfterCallStrong t) := by
  apply R13Shards.Hoare.store_fall
  intro F s x v mem' h hx hv hm
  obtain ⟨w, rfl⟩ := PtxP1.eval_is_word_op hv
  have hs := panMemStoresHOL_word_spec (s := s) (x := x) (w := .word w)
    (mem' := mem') (by simpa only [flattenHOL] using hm)
  apply txAfterCallStrong_store_bo h hoff hs.1 _ hs.2.2
  have he := eval_add_global_const hx
  obtain ⟨S, Nd, hWT, _⟩ := h.2.2.2.2
  have hb := (ivl_allocated_bound h.1.1.1.2
    (bo_words hWT.2.2.1 h.1.2.bo_nz).1).2
  have hoff64 : off < 2 ^ 64 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
    rcases hoff with rfl | rfl | rfl | rfl <;> norm_num
  have hsum : globN s "bo" + off < 2 ^ 64 := by
    dsimp at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
    rcases hoff with rfl | rfl | rfl | rfl <;> omega
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff64, Nat.mod_eq_of_lt hsum] using he

/-- The four consecutive block-total writes preserve the strong cut at zero cost. -/
theorem phase4TotalStores_cut {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn TxAfterCallStrong tail b) :
    TerminatingProgBoundedOn TxAfterCallStrong
      (spinePlug 5 (spineAt 114 ptxCode) tail) b := by
  have hb : TerminatingProgBoundedOn TxAfterCallStrong
      (spinePlug 5 (spineAt 114 ptxCode) tail) (0 + (0 + (0 + (0 + b)))) := by
    unfold ptxCode
    refine seq_bound_trans (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
      (hoare_store_bo_total 0 (by simp) _ _) ?_
    refine seq_bound_trans (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
      (hoare_store_bo_total 8 (by simp) _ _) ?_
    refine seq_bound_trans (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
      (hoare_store_bo_total 48 (by simp) _ _) ?_
    refine seq_bound_trans (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
      (hoare_store_bo_total 16 (by simp) _ _) ?_
    change TerminatingProgBoundedOn TxAfterCallStrong (.seq .skip tail) b
    intro F s hc hp hnt
    simpa only [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_skip] using
      htail s hc hp (by simpa only [evaluateHOLFiniteState_seq_line780,
        evaluateHOLFiniteState_skip] using hnt)
  intro F s hc hp
  simpa only [Nat.zero_add] using hb s hc hp

/-- State-gas normalization, regular-gas computation, and all block totals. -/
theorem phase4Totals_cut (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn TxAfterCallStrong tail b) :
    TerminatingProgBoundedOn TxAfterCallStrong
      (spinePlug 9 (spineAt 110 ptxCode) tail) (K.max + b + 1) := by
  have hb : TerminatingProgBoundedOn TxAfterCallStrong
      (spinePlug 9 (spineAt 110 ptxCode) tail) (0 + (K.max + b + 1)) := by
    unfold ptxCode
    refine TerminatingProgBoundedOn.dec_onLocals localsOnly_txAfterCallStrong _ (by decide) _ _ ?_
    refine TerminatingProgBoundedOn.dec_onLocals localsOnly_txAfterCallStrong _ (by decide) _ _ ?_
    refine seq_bound_trans (Q := TxAfterCallStrong) ?_ ?_ ?_
    · exact TerminatingProgBoundedOn.ite_on
        (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s .local _ _))
        (TerminatingProgBoundedOn.of_clock clock_skip)
    · apply Hoare.ite
      · apply Hoare.mono (P' := TxAfterCallStrong) _ (fun _ hp => hp.1)
        exact Hoare.assign
          (fun s v hp _ _ => LocalsOnly.setVar localsOnly_txAfterCallStrong
            (name := ofString "tx_state_gas_nat") (by decide) v s hp)
          (fun _ _ hr => absurd hr (by simp))
      · exact Hoare.skip (fun _ hp _ => hp.1)
      · exact fun _ _ hr => absurd hr (by simp)
    · refine TerminatingProgBoundedOn.decCall_on h.fb_max _ _ _
        (txAfterCallStrong_guest_entry _ _)
        (resume_ro_txAfterCallStrong h.ro_max (by decide) _) ?_
      have hh := @phase4TotalStores_cut tail b htail
      unfold ptxCode at hh
      intro F s hc hp
      exact hh s hc hp
  intro F s hc hp
  simpa only [Nat.zero_add] using hb s hc hp

/-- The first twenty Phase-4 steps preserve the complete output/log invariant. -/
theorem phase4CreditTotals_cut (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn TxAfterCallStrong tail b) :
    TerminatingProgBoundedOn TxAfterCallStrong
      (spinePlug 20 (spineAt 99 ptxCode) tail)
      (phase4CreditCost + (K.max + 1) + b) := by
  have hb := @phase4CreditPrefix_cut h _ _ (phase4Totals_cut h htail)
  have he : spinePlug 20 (spineAt 99 ptxCode) tail =
      phase4CreditPrefix (spinePlug 9 (spineAt 110 ptxCode) tail) := by
    unfold phase4CreditPrefix ptxCode
    rfl
  rw [he]
  intro F s hc hp
  have hr := hb s hc hp
  convert hr using 1 <;> omega

/-- Empty constructor results need no backing-array cell or log-entry reads. -/
theorem logsListOK_empty {F : Type} {s : PanSemStateFiniteExact 64 F}
    {logs : Nat} (hw : WordsOK s (logs, 24)) (ha : Allocated s (logs, 24))
    (hn : memW s (logs + 8) = 0) : LogsListOK s logs := by
  refine Or.inr ⟨hw, ha, ?_, ?_, ?_⟩
  · rw [hn]; norm_num
  · rw [hn]; exact Nat.zero_le _
  · intro i hi
    rw [hn] at hi
    omega

/-- Separation of an empty list only needs its header; the live array is empty. -/
theorem logsLiveOwned_empty {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {logs : Nat}
    (ha : Allocated s (memW s logs, 0))
    (hd : ∀ j ∈ worldOwned s S Nd, Disj (logs, 24) j)
    (hn : memW s (logs + 8) = 0) : LogsLiveOwned s S Nd logs := by
  intro _
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hn, Nat.mul_zero] using ha
  · intro i hi j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact hd j hj
    · exact Or.inl (by simp [hn])
  · intro i hi
    rw [hn] at hi
    omega

/-- The two fresh blocks returned by `lst_new(8,1)` establish the receipt guard. -/
theorem fresh_empty_logs {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {logs : Nat} (hA : ArenaOK s)
    (hh : FreshBlock s post logs 24)
    (hb : FreshBlock s post (memW post logs) 8)
    (hd : IvlsDisj [(logs, 24), (memW post logs, 8)] (worldOwned post S Nd))
    (hn : memW post (logs + 8) = 0) :
    LogsListOK post logs ∧ LogsLiveOwned post S Nd logs ∧ LogsDisjFixed post logs := by
  have hhi : Inside (logs, 24) sourceBase (globN post "heap_ptr") := by
    have h := hh.2.1
    change Inside (logs, 24) (globN s "heap_ptr") (globN post "heap_ptr") at h
    exact ⟨hA.1.trans h.1, h.2⟩
  have hbi : Inside (memW post logs, 0) sourceBase (globN post "heap_ptr") := by
    have h := hb.2.1
    change Inside (memW post logs, 8) (globN s "heap_ptr") (globN post "heap_ptr") at h
    constructor
    · exact hA.1.trans h.1
    · have := h.2; dsimp at this ⊢; omega
  have ho := logsLiveOwned_empty (S := S) (Nd := Nd) (Or.inl hbi)
    (fun j hj => hd _ (by simp) j hj) hn
  exact ⟨logsListOK_empty hh.2.2 (Or.inl hhi) hn, ho, logsLiveOwned_disjFixed ho⟩

/-- An explicit world typing witnesses ownership of the selected local log list. -/
def LogsWorldOwned {F : Type} (s : PanSemStateFiniteExact 64 F) (logs : Nat) : Prop :=
  ∃ S Nd, WorldTypedWith s S Nd ∧ LogsLiveOwned s S Nd logs

theorem logsWorldOwned_with_locals {F : Type} {s : PanSemStateFiniteExact 64 F}
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) {logs : Nat}
    (h : LogsWorldOwned s logs) : LogsWorldOwned {s with locals := locals, clock := k} logs := by
  obtain ⟨S, Nd, hw, ho⟩ := h
  exact ⟨S, Nd, (R13Shards.worldTypedWith_with_locals s locals k S Nd).mpr hw, ho⟩

theorem logsWorldOwned_scratchStep {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {logs : Nat}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {r : Option (PanSemResultExact 64)}
    (hs : WorldStep R gw keep Q s r post) (hA : ArenaReady s)
    (hgrow : AllocatorGrows s post) (hl : LogsListOK s logs)
    (ho : LogsWorldOwned s logs)
    {gs : List (String × Nat × Nat)} (hgs : ScratchSpec gs)
    (hR : R s = gs.map (fun e => bufferRegion s (e.1, e.2.2)))
    (hsys : ofString "vm_system_address" ∉ gw.map ofString) :
    LogsListOK post logs ∧ LogsWorldOwned post logs := by
  obtain ⟨S, Nd, hWT, hd⟩ := ho
  have hRd : IvlsDisj (R s) (worldTypedIvls s S Nd) := by
    rw [hR]
    intro i hi j hj
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hi
    exact bufferRegion_disj_le hWT (e.1, e.2.1) (hgs e he).1
      (hgs e he).2.1 e.2.2 (hgs e he).2.2.2 j hj
  obtain ⟨S', Nd', _, hWT', hog, hfr, _⟩ := hs.2.2.2.2 S Nd hWT hRd
  have hfr' : FrameOutside s post
      (worldOwned s S Nd ++ gs.map (fun e => bufferRegion s (e.1, e.2.2)) ++ [freeGap s])
      (heapFree s) := by simpa only [hR] using hfr
  have hp := logsLiveOwned_scratchStep hgs hA.2 hs.1.2 hA.1 hs.1.1
    hWT hgrow hl hd (R16Shards.globN_eq_of_lookup (hs.2.2.1 _ hsys)) hog hfr'
  exact ⟨hp.1, S', Nd', hWT', hp.2⟩

theorem logsWorldOwned_heapStep_header {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {logs : Nat}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {r : Option (PanSemResultExact 64)} {keep : List (String × List Nat)}
    (hs : WorldStep (fun _ => []) ["heap_ptr"] keep Q s r post)
    (hA : ArenaReady s) (hl : LogsListOK s logs) (ho : LogsWorldOwned s logs)
    (hn : logs ≠ 0) :
    memW post logs = memW s logs ∧ memW post (logs + 8) = memW s (logs + 8) := by
  obtain ⟨S, Nd, hWT, hd⟩ := ho
  have hgrow : AllocatorGrows s post := ⟨hs.2.1, by
    have he : globN post "scratch_ptr" = globN s "scratch_ptr" :=
      R16Shards.globN_eq_of_lookup (hs.2.2.1 _ (by decide))
    omega⟩
  obtain ⟨S', Nd', _, _, hog, hfr, _⟩ := hs.2.2.2.2 S Nd hWT (by intro i hi; cases hi)
  have hl' := hl.resolve_left hn
  have hh := allocated_ivl_survives_step hA.2 hs.1.2 hgrow
    (worldOwned_zero_aligned hWT) (by intro j hj; cases hj) hog hfr
    hl'.1.1 (by norm_num : 24 % 8 = 0) hl'.2.1
    (fun j hj => (hd hn).2.1 _ (by simp) j hj) (by intro j hj; cases hj)
  have hb := (ivl_allocated_bound hA.2 hl'.2.1).2
  exact ⟨memW_eq_of_ivlUnhit hh.2.2 hl'.1.1 hb ⟨by omega, by omega⟩,
    memW_eq_of_ivlUnhit hh.2.2 (by have := hl'.1.1; omega) hb ⟨by omega, by omega⟩⟩

/-- Heap-only calls retain every source-array entry used by the copy loop. -/
theorem logsWorldOwned_heapStep_array {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {logs : Nat}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {r : Option (PanSemResultExact 64)} {keep : List (String × List Nat)}
    (hs : WorldStep (fun _ => []) ["heap_ptr"] keep Q s r post)
    (hA : ArenaReady s) (hl : LogsListOK s logs) (ho : LogsWorldOwned s logs)
    (hn : logs ≠ 0) :
    ∀ i, i < memW s (logs + 8) →
      memW post (memW s logs + 8 * i) = memW s (memW s logs + 8 * i) := by
  obtain ⟨S, Nd, hWT, hd⟩ := ho
  have hgrow : AllocatorGrows s post := ⟨hs.2.1, by
    have he : globN post "scratch_ptr" = globN s "scratch_ptr" :=
      R16Shards.globN_eq_of_lookup (hs.2.2.1 _ (by decide))
    omega⟩
  obtain ⟨S', Nd', _, _, hog, hfr, _⟩ := hs.2.2.2.2 S Nd hWT (by intro i hi; cases hi)
  exact (logsLiveOwned_array_survives hA.2 hs.1.2 hA.1 hgrow hl hd hn
    (worldOwned_zero_aligned hWT) (by intro j hj; cases hj) hog hfr
    (by intro j hj; cases hj)).2.2

/-- Preserve source ownership with the same witnesses used by a heap call's
return contract. -/
theorem logsWorldOwned_heapStep_joint {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {logs : Nat}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {r : Option (PanSemResultExact 64)} {keep : List (String × List Nat)}
    (hs : WorldStep (fun _ => []) ["heap_ptr"] keep Q s r post)
    (hA : ArenaReady s) (hl : LogsListOK s logs) (ho : LogsWorldOwned s logs) :
    ∃ S Nd, WorldTypedWith post S Nd ∧ LogsLiveOwned post S Nd logs ∧ Q s r post S Nd := by
  obtain ⟨S, Nd, hWT, hd⟩ := ho
  have hgrow : AllocatorGrows s post := ⟨hs.2.1, by
    have he : globN post "scratch_ptr" = globN s "scratch_ptr" :=
      R16Shards.globN_eq_of_lookup (hs.2.2.1 _ (by decide))
    omega⟩
  obtain ⟨S', Nd', _, hWT', hog, hfr, hQ⟩ := hs.2.2.2.2 S Nd hWT (by intro i hi; cases hi)
  refine ⟨S', Nd', hWT', ?_, hQ⟩
  exact logsLiveOwned_survives hA.2 hs.1.2 hA.1 hgrow hl hd
    (R16Shards.globN_eq_of_lookup (hs.2.2.1 _ (by decide)))
    (worldOwned_zero_aligned hWT) (by intro j hj; cases hj) hog hfr
    (by intro j hj; cases hj) (by intro j hj; cases hj)
    (by intro i hi j hj; cases hj)

/-- Restore caller locals without discarding the allocator's return predicate. -/
theorem heapStep_restore_locals {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {r : Option (PanSemResultExact 64)} {keep : List (String × List Nat)}
    (hs : WorldStep (fun _ => []) ["heap_ptr"] keep Q s r post)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    ∀ S Nd, WorldTypedWith {s with locals := locals, clock := k} S Nd →
      ∃ S' Nd', WorldTypedWith post S' Nd' ∧ Q s r post S' Nd' := by
  intro S Nd hW
  have hWs := (R13Shards.worldTypedWith_with_locals s locals k S Nd).mp hW
  obtain ⟨S', Nd', _, hW', _, _, hQ⟩ := hs.2.2.2.2 S Nd hWs (by intro i hi; cases hi)
  exact ⟨S', Nd', hW', hQ⟩

def Phase4ReceiptReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => TxAfterCallStrong s ∧ LogsListOK s (locN s "logs") ∧
    LogsDisjFixed s (locN s "logs") ∧ LogsWorldOwned s (locN s "logs")

theorem lst_new_receiptReady_resume (h : PtxCallees) :
    DecCallResumeOn TxAfterCallStrong Phase4ReceiptReady (ofString "logs")
      (ofString "lst_new") [.const 8, .const 1] := by
  intro F s vs body callee ret v post hc hp ha hl hr
  have hlc := R13Shards.lookup_lst_new
  rw [← hc] at hlc
  obtain ⟨_, he, hcap⟩ := callee_param_two_exp s (ofString "lst_new")
    (ofString "esz") (ofString "cap") .one .one _ _ hlc
    (.const 8) (.const 1) (.val (.word 8)) (.val (.word 1))
    vs body callee ret rfl rfl ha hl
  let ent := callEntryStateHOLFinite s callee
  have he8 : locN ent "esz" = 8 := by simp [ent, locN, callEntryStateHOLFinite, he]
  have hc4 : locN ent "cap" = 1 := by simp [ent, locN, callEntryStateHOLFinite, hcap]
  have hmul : locN ent "esz" * locN ent "cap" < 2 ^ 64 := by rw [he8, hc4]; norm_num
  have hpos : 1 ≤ locN ent "cap" := by omega
  have hw := funSpec_at_lookup h.wk_lst_new s hc vs body callee ret hl
    (worldOK_callEntry hp.1.1 callee) (by rw [hr]; simp)
  rw [hr] at hw
  have hs := hw (Or.inl ⟨v, rfl⟩)
  obtain ⟨S, Nd, hWT, _, _⟩ := hp.2.2.2.2
  have hWTc := (R13Shards.worldTypedWith_with_locals s callee (s.clock - 1) S Nd).mpr hWT
  obtain ⟨S', Nd', _, hWT', _, _, hret⟩ := hs.2.2.2.2 S Nd hWTc
    (by intro i hi; cases hi)
  obtain ⟨w, hv, hd⟩ := hret hmul v rfl
  have ht := funSpec_at_lookup h.rt_lst_new s hc vs body callee ret hl
    (worldOK_callEntry hp.1.1 callee).1 (by rw [hr]; simp)
  rw [hr] at ht
  obtain ⟨w', hv', _, _, hf⟩ := ht v rfl
  have heq : w' = w := by rw [hv] at hv'; cases hv'; rfl
  subst w'
  obtain ⟨hh, hb, _, hn, _⟩ := hf hmul hpos
  have hb32 : FreshBlock ent post (memW post w.toNat) 8 := by
    change FreshBlock ent post (memW post w.toNat) (locN ent "esz" * locN ent "cap") at hb
    simpa only [he8, hc4] using hb
  have hd32 : IvlsDisj [(w.toNat, 24), (memW post w.toNat, 8)]
      (worldOwned post S' Nd') := by
    change IvlsDisj [(w.toNat, 24), (memW post w.toNat, locN ent "esz" * locN ent "cap")]
      (worldOwned post S' Nd') at hd
    simpa only [he8, hc4] using hd
  obtain ⟨hL, hO, hD⟩ := fresh_empty_logs (s := ent) hp.1.1.1.2 hh hb32 hd32 hn
  have hout := lst_new_txAfterCallStrong_resume h s vs body callee ret v post hc hl hr hp
  refine ⟨hout, ?_, ?_, ?_⟩
  all_goals rw [hv]; simp only [locN, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, if_pos rfl]
  · exact (R13Shards.logsListOK_with_locals post _ post.clock w.toNat).mpr hL
  · exact hD
  · exact logsWorldOwned_with_locals _ _ ⟨S', Nd', hWT', hO⟩

def Phase4LogsReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => TxAfterCallStrong s ∧
    locN s "logs" = memW s (locN s "out" + 16) ∧
    LogsListOK s (locN s "logs") ∧ LogsDisjFixed s (locN s "logs")

theorem evalAt_load_local {F : Type} (t : PanSemStateFiniteExact 64 F)
    (l : String) (k : BitVec 64) (v : ValueHOL 64)
    (h : evalAt t (.load .one (.op .add [.var .local (ofString l), .const k])) = some v) :
    ∃ a : BitVec 64, v = .val (.word a) ∧ a.toNat = memW t ((locN t l + k.toNat) % 2 ^ 64) := by
  simp [evalAt, evalHOLExact, evalListHOLExact] at h
  rcases hl : t.locals.lookup (ofString l) with _ | w
  · simp [hl] at h
  · rcases w with x | fs | ⟨nm, fs⟩
    · cases x with
      | word x =>
        simp [hl, valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact] at h
        rcases hm : t.memory (x + k) with ⟨y⟩
        refine ⟨y, by rw [← h.2, hm], ?_⟩
        have hadd : BitVec.ofNat 64 ((x.toNat + k.toNat) % 2 ^ 64) = x + k := by
          apply BitVec.eq_of_toNat_eq
          simp [BitVec.toNat_add]
        simp only [locN, memW, hl, hadd, h.2, hm]
    · simp [hl, valueIsWord] at h
    · simp [hl, valueIsWord] at h

theorem evalAt_load_local_nonzero {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hg : GuestInv s) (l : String) (v : ValueHOL 64)
    (he : evalAt s (.load .one (.op .add [.var .local (ofString l), .const 8])) = some v) :
    locN s l ≠ 0 := by
  intro hz
  rcases hlu : s.locals.lookup (ofString l) with _ | val
  · simp [evalAt, evalHOLExact, evalListHOLExact, hlu] at he
  rcases val with w | fs | ⟨nm, fs⟩
  · cases w with
    | word w =>
      have hw : w.toNat = 0 := by simpa [locN, hlu] using hz
      have hw0 : w = 0 := BitVec.eq_of_toNat_eq hw
      subst w
      have hdom : ¬ s.memaddrs (8 : BitVec 64) := by
        rw [hg.memaddrs]
        intro hd
        have hb := ((ordinaryDomain_iff (8 : BitVec 64)).mp hd).2.1
        change sourceBase ≤ 8 at hb
        norm_num [sourceBase] at hb
      simp [evalAt, evalHOLExact, evalListHOLExact, hlu, valueIsWord, valueWord,
        wordOpHOL, wordOp, memLoadHOLExact, hdom] at he
      exact hdom he.1
  · simp [evalAt, evalHOLExact, evalListHOLExact, hlu, valueIsWord] at he
  · simp [evalAt, evalHOLExact, evalListHOLExact, hlu, valueIsWord] at he

theorem phase4LogsReady_load {F : Type} (s : PanSemStateFiniteExact 64 F)
    (v : ValueHOL 64) (h : TxAfterCallStrong s)
    (he : evalAt s (.load .one (.op .add [.var .local (ofString "out"), .const 16])) = some v) :
    Phase4LogsReady (setVarHOLFinite (ofString "logs") v s) := by
  obtain ⟨w, rfl, hw⟩ := evalAt_load_local s "out" 16 v he
  have hb := (ivl_allocated_bound h.1.1.1.2 (Or.inl h.2.2.1)).2
  have hlt : locN s "out" + 16 < 2 ^ 64 := by dsimp at hb; omega
  have hwe : w.toNat = memW s (locN s "out" + 16) := by
    simpa only [show (16 : BitVec 64).toNat = 16 from rfl, Nat.mod_eq_of_lt hlt] using hw
  let post := setVarHOLFinite (ofString "logs") (.val (.word w)) s
  have hout : locN post "out" = locN s "out" := by
    simp [post, locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "logs" ≠ ofString "out" from by decide]
  have hlogs : locN post "logs" = w.toNat := by
    simp [post, locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  have hp : TxAfterCallStrong post :=
    LocalsOnly.setVar localsOnly_txAfterCallStrong (by decide) _ s h
  refine ⟨hp, ?_, ?_, ?_⟩
  · change locN post "logs" = memW s (locN post "out" + 16)
    rw [hlogs, hout, hwe]
  · rw [hlogs, hwe]
    exact (R13Shards.logsListOK_with_locals s post.locals s.clock _).mpr h.2.2.2.1
  · obtain ⟨S, Nd, _, _, ho⟩ := h.2.2.2.2
    rw [hlogs, hwe]
    exact logsLiveOwned_disjFixed (s := post) ho

/-- The credit/totals prefix ends with the live-log receipt guard established. -/
theorem phase4ThroughLogs_cut (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn Phase4LogsReady tail b) :
    TerminatingProgBoundedOn TxAfterCallStrong
      (spinePlug 21 (spineAt 99 ptxCode) tail)
      (phase4CreditCost + (K.max + 1) + b) := by
  have hl : TerminatingProgBoundedOn TxAfterCallStrong
      (.dec (ofString "logs") .one
        (.load .one (.op .add [.var .local (ofString "out"), .const 16])) tail) b :=
    dec_bound_trans (fun s v hp he => phase4LogsReady_load s v hp he) htail
  have hb := @phase4CreditTotals_cut h _ _ hl
  have he : spinePlug 21 (spineAt 99 ptxCode) tail =
      spinePlug 20 (spineAt 99 ptxCode)
        (.dec (ofString "logs") .one
          (.load .one (.op .add [.var .local (ofString "out"), .const 16])) tail) := by
    unfold ptxCode
    rfl
  rw [he]
  intro F s hc hp
  exact hb s hc hp

theorem phase4NullLogs_cut (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn Phase4ReceiptReady tail b) :
    TerminatingProgBoundedOn Phase4LogsReady
      (spinePlug 1 (spineAt 120 ptxCode) tail) ((K.lst_new + 1) + b) := by
  have hb : TerminatingProgBoundedOn Phase4LogsReady
      (spinePlug 1 (spineAt 120 ptxCode) tail) (max (K.lst_new + 1) 0 + b) := by
    unfold ptxCode
    refine seq_bound_trans (Q := Phase4ReceiptReady) ?_ ?_ htail
    · apply TerminatingProgBoundedOn.ite_on
      · exact TerminatingProgBoundedOn.call_on h.fb_lst_new _ _
          (fun s vs body callee ret hc hp ha hl => guestInv_callEntry s callee hp.1.1.1.1.1)
      · exact TerminatingProgBoundedOn.of_clock clock_skip
    · apply Hoare.ite
      · apply Hoare.mono (P' := TxAfterCallStrong) _ (fun _ hp => hp.1.1)
        exact Hoare.callLocal_resume (lst_new_receiptReady_resume h)
      · apply Hoare.skip
        intro F s hp _
        refine ⟨hp.1.1, hp.1.2.2.1, hp.1.2.2.2, ?_⟩
        rw [hp.1.2.1]
        obtain ⟨S, Nd, hw, _, ho⟩ := hp.1.1.2.2.2.2
        exact ⟨S, Nd, hw, ho⟩
      · exact fun _ _ hr => absurd hr (by simp)
  intro F s hc hp
  simpa only [Nat.max_zero] using hb s hc hp

theorem localsOnly_phase4ReceiptReady : LocalsOnly ["index", "out", "logs"] Phase4ReceiptReady := by
  intro F s locals k hl hp
  have hg := locN_congr s locals k "logs" (hl "logs" (by simp))
  refine ⟨txAfterCallStrong_with_locals s locals k
    (hl "index" (by simp)) (hl "out" (by simp)) hp.1, ?_, ?_, ?_⟩
  · rw [hg]
    exact (R13Shards.logsListOK_with_locals s locals k _).mpr hp.2.1
  · rw [hg]; exact hp.2.2.1
  · rw [hg]; exact logsWorldOwned_with_locals locals k hp.2.2.2

theorem phase4Succeeded_cut {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn Phase4ReceiptReady tail b) :
    TerminatingProgBoundedOn Phase4ReceiptReady
      (spinePlug 2 (spineAt 121 ptxCode) tail) b := by
  have hb : TerminatingProgBoundedOn Phase4ReceiptReady
      (spinePlug 2 (spineAt 121 ptxCode) tail) (0 + b) := by
    unfold ptxCode
    refine TerminatingProgBoundedOn.dec_onLocals localsOnly_phase4ReceiptReady _ (by decide) _ _ ?_
    refine seq_bound_trans (Q := Phase4ReceiptReady) ?_ ?_ htail
    · exact TerminatingProgBoundedOn.ite_on
        (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s .local _ _))
        (TerminatingProgBoundedOn.of_clock clock_skip)
    · apply Hoare.ite
      · apply Hoare.mono (P' := Phase4ReceiptReady) _ (fun _ hp => hp.1)
        exact Hoare.assign
          (fun s v hp _ _ => LocalsOnly.setVar localsOnly_phase4ReceiptReady
            (name := ofString "succeeded") (by decide) v s hp)
          (fun _ _ hr => absurd hr (by simp))
      · exact Hoare.skip (fun _ hp _ => hp.1)
      · exact fun _ _ hr => absurd hr (by simp)
  intro F s hc hp
  simpa only [Nat.zero_add] using hb s hc hp

/-- The Phase-4 prefix reaches receipt encoding with its full entry guard. -/
theorem phase4BeforeReceipt_cut (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn Phase4ReceiptReady tail b) :
    TerminatingProgBoundedOn TxAfterCallStrong
      (spinePlug 24 (spineAt 99 ptxCode) tail)
      (phase4CreditCost + (K.max + 1) + ((K.lst_new + 1) + b)) := by
  have hb := @phase4ThroughLogs_cut h _ _
    (phase4NullLogs_cut h (phase4Succeeded_cut htail))
  have he : spinePlug 24 (spineAt 99 ptxCode) tail =
      spinePlug 21 (spineAt 99 ptxCode)
        (spinePlug 1 (spineAt 120 ptxCode)
          (spinePlug 2 (spineAt 121 ptxCode) tail)) := by
    unfold ptxCode
    rfl
  rw [he]
  intro F s hc hp
  exact hb s hc hp

def receiptScratchSpec : List (String × Nat × Nat) :=
  [("keccak_pad", 136, 136), ("keccak_st", 200, 200)]

theorem receiptScratchSpec_ok : ScratchSpec receiptScratchSpec := by
  unfold ScratchSpec receiptScratchSpec
  decide

/-- Receipt encoding preserves the message output independently of its returned slice. -/
theorem encode_receipt_output_resume (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "encode_receipt") vs =
      some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) (hp : Phase4ReceiptReady s)
    (hg : locN (callEntryStateHOLFinite s callee) "logs" = locN s "logs") :
    TxAfterCallStrong { post with locals := s.locals } := by
  have hL : LogsListOK (callEntryStateHOLFinite s callee)
      (locN (callEntryStateHOLFinite s callee) "logs") := by
    rw [hg]
    exact (R13Shards.logsListOK_with_locals s callee (s.clock - 1) _).mpr hp.2.1
  have hD : LogsDisjFixed (callEntryStateHOLFinite s callee)
      (locN (callEntryStateHOLFinite s callee) "logs") := by
    rw [hg]; exact hp.2.2.1
  have hw := funSpec_at_lookup h.wk_encode_receipt s hc vs body callee ret hl
    ⟨worldOK_callEntry hp.1.1.1 callee, hL, hD⟩ (by rw [hr]; simp)
  rw [hr] at hw
  have hs := hw (Or.inl ⟨v, rfl⟩)
  have hsc : globN post "scratch_ptr" = globN s "scratch_ptr" :=
    R16Shards.globN_eq_of_lookup (hs.2.2.1 _ (by decide))
  have hs' := R13Shards.worldStep_with_locals hs s.locals s.clock
  exact txAfterCallStrong_scratchStep
    (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])
    hs' hp.1 ⟨hs.2.1, by omega⟩ receiptScratchSpec_ok
    rfl (by decide) (by decide) (by decide) (by simp)
    (by intro k hk; simp only [List.mem_cons, List.not_mem_nil, or_false] at hk ⊢
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> simp)

/-- The receipt contract also returns bounded slice words and valid live logs. -/
theorem encode_receipt_result (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "encode_receipt") vs =
      some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) (hp : Phase4ReceiptReady s)
    (hg : locN (callEntryStateHOLFinite s callee) "logs" = locN s "logs") :
    ∃ a b : BitVec 64, v = .rStruct [.val (.word a), .val (.word b)] ∧
      Inside (a.toNat, b.toNat) sourceBase (globN post "heap_ptr") ∧
      a.toNat < 2 ^ 61 ∧ b.toNat < 2 ^ 61 ∧
      memW post (locN s "logs" + 8) < 2 ^ 28 ∧ LogsListOK post (locN s "logs") := by
  have hL : LogsListOK (callEntryStateHOLFinite s callee)
      (locN (callEntryStateHOLFinite s callee) "logs") := by
    rw [hg]
    exact (R13Shards.logsListOK_with_locals s callee (s.clock - 1) _).mpr hp.2.1
  have hD : LogsDisjFixed (callEntryStateHOLFinite s callee)
      (locN (callEntryStateHOLFinite s callee) "logs") := by
    rw [hg]; exact hp.2.2.1
  have hw := funSpec_at_lookup h.wk_encode_receipt s hc vs body callee ret hl
    ⟨worldOK_callEntry hp.1.1.1 callee, hL, hD⟩ (by rw [hr]; simp)
  rw [hr] at hw
  have hs := hw (Or.inl ⟨v, rfl⟩)
  obtain ⟨S, Nd, hWT, _, _⟩ := hp.1.2.2.2.2
  have hWTc := (R13Shards.worldTypedWith_with_locals s callee (s.clock - 1) S Nd).mpr hWT
  have hR : IvlsDisj
      (receiptScratchSpec.map (fun e => bufferRegion (callEntryStateHOLFinite s callee) (e.1, e.2.2)))
      (worldTypedIvls (callEntryStateHOLFinite s callee) S Nd) := by
    intro i hi j hj
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hi
    exact bufferRegion_disj_le hWTc (e.1, e.2.1) (receiptScratchSpec_ok e he).1
      (receiptScratchSpec_ok e he).2.1 e.2.2 (receiptScratchSpec_ok e he).2.2.2 j hj
  obtain ⟨S', Nd', _, _, _, _, hret⟩ := hs.2.2.2.2 S Nd hWTc hR
  simpa only [hg] using hret v rfl

theorem encode_receipt_owned (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "encode_receipt") vs =
      some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) (hp : Phase4ReceiptReady s)
    (hg : locN (callEntryStateHOLFinite s callee) "logs" = locN s "logs") :
    LogsWorldOwned post (locN s "logs") := by
  have hL : LogsListOK (callEntryStateHOLFinite s callee)
      (locN (callEntryStateHOLFinite s callee) "logs") := by
    rw [hg]
    exact (R13Shards.logsListOK_with_locals s callee (s.clock - 1) _).mpr hp.2.1
  have hD : LogsDisjFixed (callEntryStateHOLFinite s callee)
      (locN (callEntryStateHOLFinite s callee) "logs") := by
    rw [hg]; exact hp.2.2.1
  have hw := funSpec_at_lookup h.wk_encode_receipt s hc vs body callee ret hl
    ⟨worldOK_callEntry hp.1.1.1 callee, hL, hD⟩ (by rw [hr]; simp)
  rw [hr] at hw
  have hs := hw (Or.inl ⟨v, rfl⟩)
  have hsc : globN post "scratch_ptr" = globN s "scratch_ptr" :=
    R16Shards.globN_eq_of_lookup (hs.2.2.1 _ (by decide))
  have hs' := R13Shards.worldStep_with_locals hs s.locals s.clock
  exact (logsWorldOwned_scratchStep hs' hp.1.1.1.1
    ⟨hs.2.1, by change globN post "scratch_ptr" ≤ globN s "scratch_ptr"; omega⟩
    hp.2.1 hp.2.2.2 receiptScratchSpec_ok rfl (by decide)).2

def Phase4ReceiptEncoded : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => TxAfterCallStrong s ∧ LogsListOK s (locN s "logs") ∧
    memW s (locN s "logs" + 8) < 2 ^ 28 ∧
    ∃ a b : BitVec 64,
      s.locals.lookup (ofString "rc") = some (.rStruct [.val (.word a), .val (.word b)]) ∧
      Inside (a.toNat, b.toNat) sourceBase (globN s "heap_ptr") ∧
      a.toNat < 2 ^ 61 ∧ b.toNat < 2 ^ 61 ∧ LogsWorldOwned s (locN s "logs")

theorem localsOnly_phase4ReceiptEncoded :
    LocalsOnly ["index", "out", "logs", "rc"] Phase4ReceiptEncoded := by
  intro F s locals k hl hp
  have hg := locN_congr s locals k "logs" (hl "logs" (by simp))
  obtain ⟨ho, hL, hn, a, b, he, hi, ha, hb, hw⟩ := hp
  refine ⟨txAfterCallStrong_with_locals s locals k
    (hl "index" (by simp)) (hl "out" (by simp)) ho, ?_, ?_, a, b, ?_, hi, ha, hb, ?_⟩
  · rw [hg]; exact (R13Shards.logsListOK_with_locals s locals k _).mpr hL
  · change memW s (locN {s with locals := locals, clock := k} "logs" + 8) < 2 ^ 28
    rw [hg]; exact hn
  · exact (hl "rc" (by simp)).trans he
  · rw [hg]; exact logsWorldOwned_with_locals locals k hw

theorem receiptEncoded_heapStep {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {r : Option (PanSemResultExact 64)}
    (hs : WorldStep (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])] Q s r post)
    (h : Phase4ReceiptEncoded s) (hn : locN s "logs" ≠ 0) :
    Phase4ReceiptEncoded {post with locals := s.locals} := by
  obtain ⟨ho, hl, hlen, a, b, he, hi, ha, hb, hw⟩ := h
  have hgrow : AllocatorGrows s post := ⟨hs.2.1, by
    have he : globN post "scratch_ptr" = globN s "scratch_ptr" :=
      R16Shards.globN_eq_of_lookup (hs.2.2.1 _ (by decide))
    omega⟩
  have hhead := logsWorldOwned_heapStep_header hs ho.1.1.1 hl hw hn
  have hlogs := logsWorldOwned_scratchStep hs ho.1.1.1 hgrow hl hw
    (gs := []) (by intro e he; cases he) rfl (by decide)
  refine ⟨txAfterCallStrong_heapStep hs ho, ?_, ?_, a, b, he, ?_, ha, hb, ?_⟩
  · exact (R13Shards.logsListOK_with_locals post s.locals post.clock _).mpr hlogs.1
  · change memW post (locN s "logs" + 8) < 2 ^ 28
    rw [hhead.2]; exact hlen
  · change Inside (a.toNat, b.toNat) sourceBase (globN post "heap_ptr")
    unfold Inside at hi ⊢; have := hs.2.1; omega
  · exact logsWorldOwned_with_locals s.locals post.clock hlogs.2

def Phase4LogCountReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => Phase4ReceiptEncoded s ∧ locN s "nl" = memW s (locN s "logs" + 8) ∧ locN s "logs" ≠ 0

theorem phase4LogCount_load {F : Type} (s : PanSemStateFiniteExact 64 F)
    (v : ValueHOL 64) (h : Phase4ReceiptEncoded s)
    (he : evalAt s (.load .one (.op .add [.var .local (ofString "logs"), .const 8])) = some v) :
    Phase4LogCountReady (setVarHOLFinite (ofString "nl") v s) := by
  have hn := evalAt_load_local_nonzero s h.1.1.1.1.1 "logs" v he
  obtain ⟨w, rfl, hw⟩ := evalAt_load_local s "logs" 8 v he
  have hlt : locN s "logs" + 8 < 2 ^ 64 := by
    rcases h.2.1 with hz | hl
    · rw [hz]; norm_num
    · have hb := (ivl_allocated_bound h.1.1.1.1.2 hl.2.1).2
      dsimp at hb; omega
  have hwe : w.toNat = memW s (locN s "logs" + 8) := by
    simpa only [show (8 : BitVec 64).toNat = 8 from rfl, Nat.mod_eq_of_lt hlt] using hw
  refine ⟨LocalsOnly.setVar localsOnly_phase4ReceiptEncoded (by decide) _ s h, ?_⟩
  simpa [locN, memW, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
    show ofString "nl" ≠ ofString "logs" from by decide] using And.intro hwe hn

/-- Loading the source length retains a word-shaped operand, including zero. -/
theorem phase4LogCount_load_typed {F : Type} (s : PanSemStateFiniteExact 64 F)
    (v : ValueHOL 64) (h : Phase4ReceiptEncoded s)
    (he : evalAt s (.load .one (.op .add [.var .local (ofString "logs"), .const 8])) = some v) :
    let t := setVarHOLFinite (ofString "nl") v s
    Phase4LogCountReady t ∧
      ∃ n : BitVec 64, t.locals.lookup (ofString "nl") = some (.val (.word n)) := by
  refine ⟨phase4LogCount_load s v h he, ?_⟩
  obtain ⟨w, rfl, _⟩ := evalAt_load_local s "logs" 8 v he
  exact ⟨w, by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]⟩

theorem localsOnly_phase4LogCountReady :
    LocalsOnly ["index", "out", "logs", "rc", "nl"] Phase4LogCountReady := by
  intro F s locals k hl hp
  refine ⟨localsOnly_phase4ReceiptEncoded s locals k (fun n hn => hl n (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn ⊢
    rcases hn with rfl | rfl | rfl | rfl <;> simp)) hp.1, ?_⟩
  change locN {s with locals := locals, clock := k} "nl" =
    memW s (locN {s with locals := locals, clock := k} "logs" + 8) ∧
      locN {s with locals := locals, clock := k} "logs" ≠ 0
  rw [locN_congr s locals k "nl" (hl "nl" (by simp)),
    locN_congr s locals k "logs" (hl "logs" (by simp))]
  exact hp.2

def Phase4LogPointersReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => Phase4LogCountReady s ∧ locN s "lp" = memW s (locN s "logs")

theorem phase4LogPointer_load {F : Type} (s : PanSemStateFiniteExact 64 F)
    (v : ValueHOL 64) (h : Phase4LogCountReady s)
    (he : evalAt s (.load .one (.op .add [.var .local (ofString "logs"), .const 0])) = some v) :
    Phase4LogPointersReady (setVarHOLFinite (ofString "lp") v s) := by
  obtain ⟨w, rfl, hw⟩ := evalAt_load_local s "logs" 0 v he
  have hlt : locN s "logs" < 2 ^ 64 := by
    rcases h.1.2.1 with hz | hl
    · rw [hz]; norm_num
    · have hb := (ivl_allocated_bound h.1.1.1.1.1.2 hl.2.1).2
      dsimp at hb; omega
  have hwe : w.toNat = memW s (locN s "logs") := by
    simpa only [show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero,
      Nat.mod_eq_of_lt hlt] using hw
  refine ⟨LocalsOnly.setVar localsOnly_phase4LogCountReady (by decide) _ s h, ?_⟩
  simpa [locN, memW, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
    show ofString "lp" ≠ ofString "logs" from by decide] using hwe

/-- Loading the source pointer preserves the typed length and supplies a typed pointer. -/
theorem phase4LogPointer_load_typed {F : Type} (s : PanSemStateFiniteExact 64 F)
    (v : ValueHOL 64) (h : Phase4LogCountReady s)
    (hn : ∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n)))
    (he : evalAt s (.load .one (.op .add [.var .local (ofString "logs"), .const 0])) = some v) :
    let t := setVarHOLFinite (ofString "lp") v s
    Phase4LogPointersReady t ∧ ∃ n p : BitVec 64,
      t.locals.lookup (ofString "nl") = some (.val (.word n)) ∧
      t.locals.lookup (ofString "lp") = some (.val (.word p)) := by
  refine ⟨phase4LogPointer_load s v h he, ?_⟩
  obtain ⟨n, hn⟩ := hn
  obtain ⟨p, rfl, _⟩ := evalAt_load_local s "logs" 0 v he
  refine ⟨n, p, ?_, ?_⟩
  · simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "lp" ≠ ofString "nl" by decide] using hn
  · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]

theorem logPointers_heapStep {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {r : Option (PanSemResultExact 64)}
    (hs : WorldStep (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])] Q s r post)
    (h : Phase4LogPointersReady s) (hn : locN s "logs" ≠ 0) :
    Phase4LogPointersReady {post with locals := s.locals} := by
  obtain ⟨a, b, _, _, _, _, hw⟩ := h.1.1.2.2.2
  have hh := logsWorldOwned_heapStep_header hs h.1.1.1.1.1.1 h.1.1.2.1 hw hn
  refine ⟨⟨receiptEncoded_heapStep hs h.1.1 hn, ?_, hn⟩, ?_⟩
  · change locN s "nl" = memW post (locN s "logs" + 8)
    rw [hh.2]; exact h.1.2.1
  · change locN s "lp" = memW post (locN s "logs")
    rw [hh.1]; exact h.2

theorem localsOnly_phase4LogPointersReady :
    LocalsOnly ["index", "out", "logs", "rc", "nl", "lp"] Phase4LogPointersReady := by
  intro F s locals k hl hp
  refine ⟨localsOnly_phase4LogCountReady s locals k (fun n hn => hl n (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn ⊢
    rcases hn with rfl | rfl | rfl | rfl | rfl <;> simp)) hp.1, ?_⟩
  change locN {s with locals := locals, clock := k} "lp" =
    memW s (locN {s with locals := locals, clock := k} "logs")
  rw [locN_congr s locals k "lp" (hl "lp" (by simp)),
    locN_congr s locals k "logs" (hl "logs" (by simp))]
  exact hp.2

theorem lst_push_logPointers_resume (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_push") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post))
    (hp : Phase4LogPointersReady s) (hn : locN s "logs" ≠ 0)
    (harg : BoListArg (callEntryStateHOLFinite s callee)) :
    Phase4LogPointersReady (setVarHOLFinite (ofString "slot") v {post with locals := s.locals}) := by
  have hw := funSpec_at_lookup h.wk_lst_push s hc vs body callee ret hl harg (by rw [hr]; simp)
  rw [hr] at hw
  have hs := hw (Or.inl ⟨v, rfl⟩)
  have hs' := R13Shards.worldStep_with_locals hs s.locals s.clock
  exact LocalsOnly.setVar localsOnly_phase4LogPointersReady (by decide) v _
    (logPointers_heapStep hs' hp hn)

theorem lst_push_bo40_arg {F : Type} (s : PanSemStateFiniteExact 64 F)
    (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (hc : s.code = originalRuntimeCode) (hp : TxWorld s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.load .one (.op .add [.var .global (ofString "bo"), .const 40]), .const 8] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_push") vs = some (body, callee, ret)) :
    BoListArg (callEntryStateHOLFinite s callee) ∧
      locN (callEntryStateHOLFinite s callee) "l" = memW s (globN s "bo" + 40) := by
  have ha' := ha
  rw [evalListHOLFinite_eq_toExact] at ha'
  rcases hload : evalAt s (.load .one (.op .add [.var .global (ofString "bo"), .const 40])) with _ | vl
  · simp only [evalListHOLExact, hload] at ha'; cases ha'
  obtain ⟨w, rfl, hw⟩ := evalAt_loadG s "bo" 40 vl hload
  have hparams := callee_param_two_exp s (ofString "lst_push") (ofString "l") (ofString "esz")
    .one .one _ _ (by rw [hc]; exact lookup_lst_push)
    (.load .one (.op .add [.var .global (ofString "bo"), .const 40])) (.const 8)
    (.val (.word w)) (.val (.word 8)) vs body callee ret hload rfl ha hl
  have hle : locN (callEntryStateHOLFinite s callee) "l" = memW s (globN s "bo" + 40) := by
    simpa only [locN, callEntryStateHOLFinite, hparams.2.1,
      show (40 : BitVec 64).toNat = 40 from rfl] using hw
  refine ⟨⟨worldOK_callEntry hp.1 callee, hp.2.bo_nz, Or.inl hle, ?_⟩, hle⟩
  simp only [locN, callEntryStateHOLFinite, hparams.2.2]
  rfl

/-- The strengthened transaction environment discharges the concrete push
entry guard for the block log list. -/
theorem lst_push_bo40_arg_backing {F : Type} (s : PanSemStateFiniteExact 64 F)
    (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (hc : s.code = originalRuntimeCode) (hp : TxWorld s) (hb : TxBacking s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.load .one (.op .add [.var .global (ofString "bo"), .const 40]), .const 8] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_push") vs = some (body, callee, ret)) :
    BoListArgStrong (callEntryStateHOLFinite s callee) := by
  obtain ⟨harg, he⟩ := lst_push_bo40_arg s vs body callee ret hc hp ha hl
  refine ⟨harg.1, harg, ?_⟩
  rw [he]
  exact hb.1

theorem lst_push_slot_result (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_push") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post))
    (harg : BoListArg (callEntryStateHOLFinite s callee)) :
    ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat % 8 = 0 ∧
      Inside (w.toNat, 8) (memW post (locN (callEntryStateHOLFinite s callee) "l"))
        (memW post (locN (callEntryStateHOLFinite s callee) "l") +
          8 * memW post (locN (callEntryStateHOLFinite s callee) "l" + 16)) := by
  have hw := funSpec_at_lookup h.wk_lst_push s hc vs body callee ret hl harg (by rw [hr]; simp)
  rw [hr] at hw
  have hs := hw (Or.inl ⟨v, rfl⟩)
  obtain ⟨S, hW⟩ := harg.1.2
  obtain ⟨Nd, hTr⟩ := hW.2.2.2
  have hWT : WorldTypedWith (callEntryStateHOLFinite s callee) S Nd :=
    ⟨hW.1, hW.2.1, hW.2.2.1, hTr⟩
  obtain ⟨_, _, _, _, _, _, hret⟩ := hs.2.2.2.2 S Nd hWT (by intro i hi; cases hi)
  exact hret v rfl

theorem lst_push_bo40_slot_result (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : TxWorld s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.load .one (.op .add [.var .global (ofString "bo"), .const 40]), .const 8] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_push") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat % 8 = 0 ∧
      Inside (w.toNat, 8) (memW post (memW post (globN post "bo" + 40)))
        (memW post (memW post (globN post "bo" + 40)) +
          8 * memW post (memW post (globN post "bo" + 40) + 16)) := by
  have harg := lst_push_bo40_arg s vs body callee ret hc hp ha hl
  have hw := funSpec_at_lookup h.wk_lst_push s hc vs body callee ret hl harg.1 (by rw [hr]; simp)
  rw [hr] at hw
  have hs := hw (Or.inl ⟨v, rfl⟩)
  have hbo : globN post "bo" = globN s "bo" :=
    R16Shards.globN_eq_of_lookup (hs.2.2.1 _ (by decide))
  have hm : memW post (globN s "bo" + 40) = memW s (globN s "bo" + 40) :=
    hs.2.2.2.1 ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])
      (by simp) hp.2.bo_nz 40 (by simp) (by intro i hi; cases hi)
  obtain ⟨w, hv, hal, hin⟩ := lst_push_slot_result h s vs body callee ret v post hc hl hr harg.1
  refine ⟨w, hv, hal, ?_⟩
  rw [hbo, hm]
  simpa only [harg.2] using hin

def receiptArray {F : Type} (s : PanSemStateFiniteExact 64 F) : Ivl :=
  (memW s (globN s "bo" + 32), 16 * memW s (globN s "bo" + 80) + 16)

theorem receiptArray_words {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hF : FixedTyped s) (hE : TxEnv s) : Allocated s (receiptArray s) ∧ WordsOK s (receiptArray s) := by
  have hb : receiptArray s ∈ blockOutObjects s := by
    unfold receiptArray blockOutObjects
    simp [hE.bo_nz, hE.bo32]
  exact (hF.1 _ (List.mem_append_left _ (List.mem_append_right _ hb))).resolve_left
    (by simp [receiptArray])

def receiptDst (high : Bool) : ExpHOL 64 :=
  .op .add ([.load .one (.op .add [.var .global (ofString "bo"), .const 32]),
    .panop .mul [.var .local (ofString "index"), .const 16]] ++
      if high then [.const 8] else [])

theorem receiptDst_inside {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : TxAfterCallStrong s) (high : Bool) {x : BitVec 64}
    (hx : evalAt s (receiptDst high) = some (.val (.word x))) :
    Inside (x.toNat, 8) (receiptArray s).1 ((receiptArray s).1 + (receiptArray s).2) := by
  have hE := h.1.2
  obtain ⟨S, Nd, hW, _, _⟩ := h.2.2.2.2
  have hhi := (ivl_allocated_bound h.1.1.1.2 (receiptArray_words hW.2.2.1 hE).1).2
  dsimp only [receiptArray] at hhi ⊢
  rcases hld : evalAt s (.load .one (.op .add [.var .global (ofString "bo"), .const 32])) with _ | vbase
  · cases high <;> simp [receiptDst, evalAt, evalHOLExact, evalListHOLExact] at hx hld
    all_goals rw [hld] at hx; simp at hx
  obtain ⟨abase, rfl, habase_nat⟩ := evalAt_loadG s "bo" 32 vbase hld
  have habase : abase.toNat = memW s (globN s "bo" + 32) := habase_nat
  cases high <;> simp only [receiptDst, Bool.false_eq_true, if_false, if_true,
    List.append_nil, List.cons_append, List.nil_append, evalAt, evalHOLExact, evalListHOLExact] at hx
  all_goals
    simp only [evalAt, evalHOLExact, evalListHOLExact] at hld
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
        subst x
        simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat] at *
        norm_num only [BitVec.toNat_ofNat] at *
        unfold Inside; dsimp only
        simp only [show (16 : BitVec 64).toNat = 16 from rfl,
          show (8 : BitVec 64).toNat = 8 from rfl,
          show (0 : BitVec 64).toNat = 0 from rfl]
        omega
    · simp [hidx_v, valueIsWord] at hx
    · simp [hidx_v, valueIsWord] at hx

theorem receiptEncoded_store {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : Phase4ReceiptEncoded s) {x : BitVec 64} (hx : s.memaddrs x)
    (hin : Inside (x.toNat, 8) (memW s (globN s "bo" + 32))
      (memW s (globN s "bo" + 32) + (16 * memW s (globN s "bo" + 80) + 16)))
    {mem' : BitVec 64 → HolWordLab 64} (hm : ∀ a, a ≠ x → mem' a = s.memory a) :
    Phase4ReceiptEncoded {s with memory := mem'} := by
  obtain ⟨ho, hl, hn, a, b, hrc, hi, ha, hb, S, Nd, hWT, hown⟩ := h
  let post := {s with memory := mem'}
  have hg : GuestInv post := guestInv_congr (s := s) rfl rfl rfl rfl ho.1.1.1.1
  obtain ⟨hWT', heq, _⟩ := store_bo_array_world ho.1.1.1 ho.1.2 hWT
    (Or.inl ⟨rfl, rfl⟩) hx hin hm
  obtain ⟨_, _, hbo⟩ := blockOutObjects_eq_list ho.1.2 hWT.1
  have hmemb : (memW s (globN s "bo" + 32), 16 * memW s (globN s "bo" + 80) + 16)
      ∈ blockOutObjects s := by rw [hbo]; simp
  have hmemf : (memW s (globN s "bo" + 32), 16 * memW s (globN s "bo" + 80) + 16)
      ∈ fixedObjects s := List.mem_append_left _ (List.mem_append_right _ hmemb)
  have hmemw : (memW s (globN s "bo" + 32), 16 * memW s (globN s "bo" + 80) + 16)
      ∈ worldOwned s S Nd := by
    unfold worldOwned; simp only [List.mem_append]; exact Or.inl (Or.inr hmemf)
  have hlogs := logsLiveOwned_single_store ho.1.1.1.2 ho.1.1.1.1 hg hl hown hm
    ⟨_, hmemw, hin⟩ heq
  refine ⟨txAfterCallStrong_store_receipt ho hx hin hm, hlogs.1, ?_, a, b, hrc, hi, ha, hb,
    S, Nd, hWT', hlogs.2⟩
  by_cases hz : locN s "logs" = 0
  · have hxlo := ((ordinaryDomain_iff x).mp (ho.1.1.1.1.memaddrs ▸ hx)).2.1
    have hbase : 8 < sourceBase := by decide
    have he : memW post 8 = memW s 8 := by
      unfold memW
      rw [show post.memory (BitVec.ofNat 64 8) = s.memory (BitVec.ofNat 64 8) from hm _ (by
        intro he; have := congrArg BitVec.toNat he; norm_num at this; omega)]
    change memW post (locN s "logs" + 8) < 2 ^ 28
    simpa only [hz, Nat.zero_add, he] using hn
  · rcases hl with he | hl
    · exact False.elim (hz he)
    have hu : IvlUnhit s post (locN s "logs", 24) :=
      ivlUnhit_single hm (by simp)
        (disj_of_inside_right hin ((hown hz).2.1 _ (by simp) _ hmemw))
    have he := memW_eq_of_ivlUnhit (a := locN s "logs" + 8) hu (by have := hl.1.1; omega)
      (ivl_allocated_bound ho.1.1.1.2 hl.2.1).2 ⟨by omega, by omega⟩
    change memW post (locN s "logs" + 8) < 2 ^ 28
    rw [he]; exact hn

theorem logPointers_worldStore {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : Phase4LogPointersReady s) (hn : locN s "logs" ≠ 0) {x : BitVec 64}
    {mem' : BitVec 64 → HolWordLab 64} (hm : ∀ a, a ≠ x → mem' a = s.memory a)
    (hpres : ∀ S Nd, WorldTypedWith s S Nd →
      WorldTypedWith {s with memory := mem'} S Nd ∧
      worldOwned {s with memory := mem'} S Nd = worldOwned s S Nd ∧
      TxEnv {s with memory := mem'})
    (hx : ∀ S Nd, WorldTypedWith s S Nd →
      ∃ i ∈ worldOwned s S Nd, Inside (x.toNat, 8) i.1 (i.1 + i.2)) :
    Phase4LogPointersReady {s with memory := mem'} := by
  obtain ⟨⟨⟨ho, hl, hlen, a, b, he, hi, ha, hb, S, Nd, hWT, hown⟩, hnl, _⟩, hlp⟩ := h
  let post := {s with memory := mem'}
  have hg : GuestInv post := guestInv_congr (s := s) rfl rfl rfl rfl ho.1.1.1.1
  obtain ⟨hWT', heq, _⟩ := hpres S Nd hWT
  obtain ⟨i, hiw, hix⟩ := hx S Nd hWT
  have hlogs := logsLiveOwned_single_store ho.1.1.1.2 ho.1.1.1.1 hg hl hown hm
    ⟨i, hiw, hix⟩ heq
  have hl' := hl.resolve_left hn
  have hu : IvlUnhit s post (locN s "logs", 24) :=
    ivlUnhit_single hm (by simp)
      (disj_of_inside_right hix ((hown hn).2.1 _ (by simp) _ hiw))
  have hbnd := (ivl_allocated_bound ho.1.1.1.2 hl'.2.1).2
  have h0 : memW post (locN s "logs") = memW s (locN s "logs") :=
    memW_eq_of_ivlUnhit hu hl'.1.1 hbnd ⟨by omega, by omega⟩
  have h8 : memW post (locN s "logs" + 8) = memW s (locN s "logs" + 8) :=
    memW_eq_of_ivlUnhit hu (by have := hl'.1.1; omega) hbnd ⟨by omega, by omega⟩
  refine ⟨⟨⟨txAfterCallStrong_worldStore ho hm hpres hx, hlogs.1, ?_,
    a, b, he, hi, ha, hb, S, Nd, hWT', hlogs.2⟩, ?_, hn⟩, ?_⟩
  · change memW post (locN s "logs" + 8) < 2 ^ 28
    rw [h8]; exact hlen
  · change locN s "nl" = memW post (locN s "logs" + 8)
    rw [h8]; exact hnl
  · change locN s "lp" = memW post (locN s "logs")
    rw [h0]; exact hlp

theorem logPointers_store_bo40 {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : Phase4LogPointersReady s) (hn : locN s "logs" ≠ 0)
    (hback : memW s (memW s (globN s "bo" + 40)) ≠ 0)
    {x : BitVec 64} (hx : s.memaddrs x)
    (hin : Inside (x.toNat, 8) (memW s (memW s (globN s "bo" + 40)))
      (memW s (memW s (globN s "bo" + 40)) +
        8 * memW s (memW s (globN s "bo" + 40) + 16)))
    {mem' : BitVec 64 → HolWordLab 64} (hm : ∀ a, a ≠ x → mem' a = s.memory a) :
    Phase4LogPointersReady {s with memory := mem'} := by
  apply logPointers_worldStore h hn hm
  · intro S Nd hWT
    exact store_bo_array_world h.1.1.1.1.1.1 h.1.1.1.1.2 hWT
      (Or.inr (Or.inl ⟨rfl, hback, rfl⟩)) hx hin hm
  · intro S Nd hWT
    obtain ⟨hc40, _, hbo⟩ := blockOutObjects_eq_list h.1.1.1.1.2 hWT.1
    let arr := (memW s (memW s (globN s "bo" + 40)),
      8 * memW s (memW s (globN s "bo" + 40) + 16))
    have hmemb : arr ∈ blockOutObjects s := by
      rw [hbo]
      simp [arr, hback, h.1.1.1.1.2.bo_nz, show memW s (memW s (globN s "bo" + 40) + 16) ≠ 0 from by omega]
    have hmemf : arr ∈ fixedObjects s := List.mem_append_left _ (List.mem_append_right _ hmemb)
    refine ⟨arr, ?_, hin⟩
    unfold worldOwned; simp only [List.mem_append]; exact Or.inl (Or.inr hmemf)

def Phase4LogSlotReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => Phase4LogPointersReady s ∧
    memW s (memW s (globN s "bo" + 40)) ≠ 0 ∧
    Inside (locN s "slot", 8) (memW s (memW s (globN s "bo" + 40)))
      (memW s (memW s (globN s "bo" + 40)) +
        8 * memW s (memW s (globN s "bo" + 40) + 16))

theorem lst_push_logSlot_resume (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4LogPointersReady s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.load .one (.op .add [.var .global (ofString "bo"), .const 40]), .const 8] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_push") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post))
    (hback : memW post (memW post (globN post "bo" + 40)) ≠ 0) :
    Phase4LogSlotReady (setVarHOLFinite (ofString "slot") v {post with locals := s.locals}) := by
  have hW := hp.1.1.1.1
  have harg := lst_push_bo40_arg s vs body callee ret hc hW ha hl
  have hptr := lst_push_logPointers_resume h s vs body callee ret v post hc hl hr hp
    hp.1.2.2 harg.1
  obtain ⟨w, rfl, _, hin⟩ := lst_push_bo40_slot_result h s vs body callee ret v post
    hc hW ha hl hr
  refine ⟨hptr, hback, ?_⟩
  simpa [locN, memW, globN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE] using hin

/-- Additional callee fact needed because a null backing pointer is omitted by
`blockOutObjects`, while `RetListSlot` alone only states interval containment. -/
def LstPushBackingNonzero : Prop :=
  FunSpec BoListArg (fun s r post => ∀ v, r = some (.returned v) →
    memW post (locN s "l") ≠ 0) (ofString "lst_push")

/-- The concrete push discharges the backing contract under the authorized
nonzero-entry guard. -/
theorem lst_push_backing_nonzero_strong (h : PtxCallees) :
    FunSpec BoListArgStrong (fun s r post => ∀ v, r = some (.returned v) →
      memW post (locN s "l") ≠ 0) (ofString "lst_push") := by
  have hlookup : originalRuntimeCode.lookup (ofString "lst_push") =
      some ([(ofString "l", .one), (ofString "esz", .one)],
        (sourceFunctionEntry Guest.Software.guestFn_lst_push).2.2.1, .one) := by
    exact lookup_lst_push
  refine ⟨_, _, _, hlookup, ?_⟩
  intro F s hc hp hvalid hnt v hv
  obtain ⟨values, hvalid⟩ := hvalid
  have hx := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup (ofString "lst_push")
    values _ s.locals _ hvalid
  simp only [lookupCodeHOLExact, hlookup] at hx
  rcases values with _ | ⟨vl, _ | ⟨ve, _ | ⟨_, _⟩⟩⟩
  · simp at hx
  · simp at hx
  swap
  · simp at hx
  · rcases vl with ⟨⟨lw⟩⟩ | _ | _
    swap
    · simp [shapeOfHOLExact, shapeEqHOL] at hx
    swap
    · simp [shapeOfHOLExact, shapeEqHOL] at hx
    rcases ve with ⟨⟨ew⟩⟩ | _ | _
    swap
    · simp [shapeOfHOLExact, shapeEqHOL] at hx
    swap
    · simp [shapeOfHOLExact, shapeEqHOL] at hx
    simp [shapeOfHOLExact, shapeEqHOL] at hx
    obtain ⟨_, hlocals⟩ := hx
    have hl : s.locals.lookup (ofString "l") = some (.val (.word lw)) := by
      have he := congrFun hlocals (ofString "l")
      simpa [FUPDATE, show ofString "esz" ≠ ofString "l" by decide,
        show ofString "l" ≠ ofString "esz" by decide] using he.symm
    have hrun : evaluateHOLFiniteState s
        (sourceFunctionEntry Guest.Software.guestFn_lst_push).2.2.1 =
        (some (.returned v), (evaluateHOLFiniteState s
          (sourceFunctionEntry Guest.Software.guestFn_lst_push).2.2.1).2) :=
      Prod.ext hv rfl
    simpa only [locN, hl] using lst_push_body_backing_nonzero h s _ lw v hc hp.1.1 hl
      (by simpa only [locN, hl] using hp.2.2) hrun

theorem resume_lst_push_logSlot (h : PtxCallees) (hnonzero : LstPushBackingNonzero) :
    DecCallResumeOn Phase4LogPointersReady Phase4LogSlotReady
      (ofString "slot") (ofString "lst_push")
      [.load .one (.op .add [.var .global (ofString "bo"), .const 40]), .const 8] := by
  intro F s vs body callee ret v post hc hp ha hl hr
  have harg := lst_push_bo40_arg s vs body callee ret hc hp.1.1.1.1 ha hl
  have hn := funSpec_at_lookup hnonzero s hc vs body callee ret hl harg.1
    (by rw [hr]; simp)
  rw [hr] at hn
  have hn' := hn v rfl
  have hw := funSpec_at_lookup h.wk_lst_push s hc vs body callee ret hl harg.1
    (by rw [hr]; simp)
  rw [hr] at hw
  have hs := hw (Or.inl ⟨v, rfl⟩)
  have hbo : globN post "bo" = globN s "bo" :=
    R16Shards.globN_eq_of_lookup (hs.2.2.1 _ (by decide))
  have hm : memW post (globN s "bo" + 40) = memW s (globN s "bo" + 40) :=
    hs.2.2.2.1 ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])
      (by simp) hp.1.1.1.1.2.bo_nz 40 (by simp) (by intro i hi; cases hi)
  apply lst_push_logSlot_resume h s vs body callee ret v post hc hp ha hl hr
  rw [hbo, hm]
  simpa only [harg.2] using hn'

/-- At a backing-aware log cut the concrete push supplies its own nonzero
result, rather than requiring the unguarded backing contract. -/
theorem resume_lst_push_logSlot_backing (h : PtxCallees) :
    DecCallResumeOn (fun s => Phase4LogPointersReady s ∧ TxBacking s) Phase4LogSlotReady
      (ofString "slot") (ofString "lst_push")
      [.load .one (.op .add [.var .global (ofString "bo"), .const 40]), .const 8] := by
  intro F s vs body callee ret v post hc hp ha hl hr
  have harg := lst_push_bo40_arg s vs body callee ret hc hp.1.1.1.1.1 ha hl
  have hstrong : BoListArgStrong (callEntryStateHOLFinite s callee) := by
    refine ⟨harg.1.1, harg.1, ?_⟩
    rw [harg.2]
    exact hp.2.1
  have hn := funSpec_at_lookup (lst_push_backing_nonzero_strong h) s hc vs body callee ret hl
    hstrong (by rw [hr]; simp)
  rw [hr] at hn
  have hw := funSpec_at_lookup h.wk_lst_push s hc vs body callee ret hl harg.1
    (by rw [hr]; simp)
  rw [hr] at hw
  have hs := hw (Or.inl ⟨v, rfl⟩)
  have hbo : globN post "bo" = globN s "bo" :=
    R16Shards.globN_eq_of_lookup (hs.2.2.1 _ (by decide))
  have hm : memW post (globN s "bo" + 40) = memW s (globN s "bo" + 40) :=
    hs.2.2.2.1 ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])
      (by simp) hp.1.1.1.1.1.2.bo_nz 40 (by simp) (by intro i hi; cases hi)
  apply lst_push_logSlot_resume h s vs body callee ret v post hc hp.1 ha hl hr
  rw [hbo, hm]
  simpa only [harg.2] using hn v rfl

theorem hoare_logSlot_store (src : ExpHOL 64)
    (hword : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
      evalAt s src = some v → ∃ w : HolWordLab 64, v = .val w) :
    Hoare Phase4LogSlotReady (.store (.var .local (ofString "slot")) src)
      (fun r t => r = none → Phase4LogPointersReady t) := by
  refine R13Shards.Hoare.store_fall fun s x v mem' hp hx hv hst => ?_
  obtain ⟨w, rfl⟩ := hword s v hv
  obtain ⟨hdom, _, hmem⟩ := R13Shards.panMemStoresHOL_word_spec
    (by simpa only [flattenHOL] using hst)
  have hslot : locN s "slot" = x.toNat := by
    have hlu : s.locals.lookup (ofString "slot") = some (.val (.word x)) := hx
    simp only [locN, hlu]
  apply logPointers_store_bo40 hp.1 hp.1.1.2.2 hp.2.1 hdom _ hmem
  simpa only [hslot] using hp.2.2

theorem store_receiptSlot (off : Bool) :
    Hoare Phase4ReceiptEncoded
      (.store (receiptDst off) (.rfield (if off then 1 else 0) (.var .local (ofString "rc"))))
      (fun r t => r = none → Phase4ReceiptEncoded t) := by
  refine R13Shards.Hoare.store_fall fun s x v mem' h hx hv hst => ?_
  obtain ⟨a, b, he, _⟩ := h.2.2.2
  have hvw : ∃ w : HolWordLab 64, v = .val w := by
    cases off <;> simp [evalAt, evalHOLExact, he] at hv <;> subst v
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  obtain ⟨w, rfl⟩ := hvw
  obtain ⟨hdom, _, hmem⟩ := R13Shards.panMemStoresHOL_word_spec (by simpa only [flattenHOL] using hst)
  exact receiptEncoded_store h hdom (receiptDst_inside h.1 off hx) hmem

theorem encode_receipt_encoded_resume (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "encode_receipt") vs =
      some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) (hp : Phase4ReceiptReady s)
    (hg : locN (callEntryStateHOLFinite s callee) "logs" = locN s "logs") :
    Phase4ReceiptEncoded (setVarHOLFinite (ofString "rc") v { post with locals := s.locals }) := by
  have ho := encode_receipt_output_resume h s vs body callee ret v post hc hl hr hp hg
  obtain ⟨a, b, hv, hi, ha, hb, hn, hL⟩ :=
    encode_receipt_result h s vs body callee ret v post hc hl hr hp hg
  let t := setVarHOLFinite (ofString "rc") v { post with locals := s.locals }
  have hlogs : locN t "logs" = locN s "logs" := by
    simp [t, locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "rc" ≠ ofString "logs" from by decide]
  refine ⟨LocalsOnly.setVar localsOnly_txAfterCallStrong (by decide) v _ ho, ?_, ?_, a, b, ?_, hi, ha, hb, ?_⟩
  · change LogsListOK t (locN t "logs")
    rw [hlogs]
    exact (R13Shards.logsListOK_with_locals post t.locals post.clock _).mpr hL
  · change memW post (locN t "logs" + 8) < 2 ^ 28
    rw [hlogs]; exact hn
  · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hv]
  · change LogsWorldOwned t (locN t "logs")
    rw [hlogs]
    exact logsWorldOwned_with_locals (s := post) t.locals post.clock
      (encode_receipt_owned h s vs body callee ret v post hc hl hr hp hg)

theorem encode_receipt_logs_param {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e1 e2 e3 : ExpHOL 64) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (hc : s.code = originalRuntimeCode)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [e1, e2, e3, .var .local (ofString "logs")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "encode_receipt") vs =
      some (body, callee, ret)) :
    locN (callEntryStateHOLFinite s callee) "logs" = locN s "logs" := by
  have ha' := ha
  rw [evalListHOLFinite_eq_toExact] at ha'
  cases h1 : evalAt s e1 with
  | none => simp only [evalAt] at h1; simp [evalListHOLExact, h1] at ha'
  | some v1 =>
    cases h2 : evalAt s e2 with
    | none => simp only [evalAt] at h1 h2; simp [evalListHOLExact, h1, h2] at ha'
    | some v2 =>
      cases h3 : evalAt s e3 with
      | none => simp only [evalAt] at h1 h2 h3; simp [evalListHOLExact, h1, h2, h3] at ha'
      | some v3 =>
        cases h4 : evalAt s (.var .local (ofString "logs")) with
        | none => simp only [evalAt] at h1 h2 h3 h4; simp [evalListHOLExact, h1, h2, h3, h4] at ha'
        | some v4 =>
          have hlc := R13Shards.lookup_encode_receipt
          rw [← hc] at hlc
          have hp := callee_param_four_exp' s (ofString "encode_receipt")
            _ _ _ _ _ _ _ _ _ _ hlc e1 e2 e3 (.var .local (ofString "logs"))
            v1 v2 v3 v4 vs body callee ret h1 h2 h3 h4 ha hl
          have hs : s.locals.lookup (ofString "logs") = some v4 := h4
          simp only [locN, callEntryStateHOLFinite, hp.2.2.2, hs]

theorem phase4EncodeReceipt_cut (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn Phase4ReceiptEncoded tail b) :
    TerminatingProgBoundedOn Phase4ReceiptReady
      (spinePlug 1 (spineAt 123 ptxCode) tail) (K.encode_receipt + b + 1) := by
  unfold ptxCode
  refine TerminatingProgBoundedOn.decCall_on h.fb_encode_receipt _ _ _ ?_ ?_ htail
  · intro F s vs body callee ret hc hp ha hl
    exact guestInv_callEntry s callee hp.1.1.1.1.1
  · intro F s vs body callee ret v post hc hp ha hl hr
    exact encode_receipt_encoded_resume h s vs body callee ret v post hc hl hr hp
      (encode_receipt_logs_param s _ _ _ vs body callee ret hc ha hl)

theorem phase4ThroughReceipt_cut (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn Phase4ReceiptEncoded tail b) :
    TerminatingProgBoundedOn TxAfterCallStrong
      (spinePlug 25 (spineAt 99 ptxCode) tail)
      (phase4CreditCost + (K.max + 1) + ((K.lst_new + 1) + (K.encode_receipt + b + 1))) := by
  have hb := @phase4BeforeReceipt_cut h _ _ (phase4EncodeReceipt_cut h htail)
  have he : spinePlug 25 (spineAt 99 ptxCode) tail =
      spinePlug 24 (spineAt 99 ptxCode) (spinePlug 1 (spineAt 123 ptxCode) tail) := by
    unfold ptxCode
    rfl
  rw [he]
  intro F s hc hp
  exact hb s hc hp

theorem phase4ReceiptStores_cut {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn Phase4ReceiptEncoded tail b) :
    TerminatingProgBoundedOn Phase4ReceiptEncoded
      (spinePlug 2 (spineAt 124 ptxCode) tail) b := by
  have hb : TerminatingProgBoundedOn Phase4ReceiptEncoded
      (spinePlug 2 (spineAt 124 ptxCode) tail) (0 + (0 + b)) := by
    unfold ptxCode
    refine seq_bound_trans (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
      (store_receiptSlot false) ?_
    exact seq_bound_trans (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
      (store_receiptSlot true) htail
  intro F s hc hp
  simpa only [Nat.zero_add] using hb s hc hp

theorem phase4ThroughReceiptStores_cut (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn Phase4ReceiptEncoded tail b) :
    TerminatingProgBoundedOn TxAfterCallStrong
      (spinePlug 27 (spineAt 99 ptxCode) tail)
      (phase4CreditCost + (K.max + 1) + ((K.lst_new + 1) + (K.encode_receipt + b + 1))) := by
  have hb := @phase4ThroughReceipt_cut h _ _ (phase4ReceiptStores_cut htail)
  have he : spinePlug 27 (spineAt 99 ptxCode) tail =
      spinePlug 25 (spineAt 99 ptxCode) (spinePlug 2 (spineAt 124 ptxCode) tail) := by
    unfold ptxCode
    rfl
  rw [he]
  intro F s hc hp
  exact hb s hc hp

theorem phase4LogPointers_cut {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn Phase4LogPointersReady tail b) :
    TerminatingProgBoundedOn Phase4ReceiptEncoded
      (spinePlug 2 (spineAt 126 ptxCode) tail) b := by
  unfold ptxCode
  exact dec_bound_trans (fun s v hp he => phase4LogCount_load s v hp he)
    (dec_bound_trans (fun s v hp he => phase4LogPointer_load s v hp he) htail)

/-- Both concrete source loads establish the typed operands required by allocation. -/
theorem phase4LogPointers_copy_cut {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn (fun s => Phase4LogPointersReady s ∧
      (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
      locN s "logs" ≠ 0 ∧
      ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p))) tail b) :
    TerminatingProgBoundedOn Phase4ReceiptEncoded
      (spinePlug 2 (spineAt 126 ptxCode) tail) b := by
  unfold ptxCode
  refine dec_bound_trans (Q := fun s => Phase4LogCountReady s ∧
    ∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n)))
    (fun s v hp he => phase4LogCount_load_typed s v hp he) ?_
  intro F t hc ht
  refine dec_bound_trans (P := fun s => Phase4LogCountReady s ∧
    ∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n)))
    ?_ htail t hc ht
  intro F s v hp he
  obtain ⟨hr, n, p, hn, hl⟩ := phase4LogPointer_load_typed s v hp.1 hp.2 he
  exact ⟨hr, ⟨n, hn⟩, hr.1.2.2, ⟨p, hl⟩⟩

theorem phase4ThroughLogPointers_cut (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn Phase4LogPointersReady tail b) :
    TerminatingProgBoundedOn TxAfterCallStrong
      (spinePlug 29 (spineAt 99 ptxCode) tail)
      (phase4CreditCost + (K.max + 1) + ((K.lst_new + 1) + (K.encode_receipt + b + 1))) := by
  have hb := @phase4ThroughReceiptStores_cut h _ _ (phase4LogPointers_cut htail)
  have he : spinePlug 29 (spineAt 99 ptxCode) tail =
      spinePlug 27 (spineAt 99 ptxCode) (spinePlug 2 (spineAt 126 ptxCode) tail) := by
    unfold ptxCode
    rfl
  rw [he]
  intro F s hc hp
  exact hb s hc hp

/-- The source-load contract needed after the log-push loop. -/
def Phase4TypedLogPointers : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => Phase4LogPointersReady s ∧
    (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
    locN s "logs" ≠ 0 ∧
    ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p))

theorem localsOnly_phase4TypedLogPointers :
    LocalsOnly ["index", "out", "logs", "rc", "nl", "lp"] Phase4TypedLogPointers := by
  intro F s locals k hl hp
  have hr := localsOnly_phase4LogPointersReady s locals k hl hp.1
  refine ⟨hr, ?_, hr.1.2.2, ?_⟩
  · obtain ⟨n, hn⟩ := hp.2.1
    exact ⟨n, (hl "nl" (by simp)).trans hn⟩
  · obtain ⟨p, hp⟩ := hp.2.2.2
    exact ⟨p, (hl "lp" (by simp)).trans hp⟩

/-- A slot write retains the word-shaped source operands. -/
theorem hoare_logSlot_store_typed (src : ExpHOL 64)
    (hword : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
      evalAt s src = some v → ∃ w : HolWordLab 64, v = .val w) :
    Hoare (fun s => Phase4LogSlotReady s ∧
      (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
      ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p)))
      (.store (.var .local (ofString "slot")) src)
      (fun r t => r = none → Phase4TypedLogPointers t) := by
  refine R13Shards.Hoare.store_fall fun s x v mem' hp hx hv hst => ?_
  obtain ⟨w, rfl⟩ := hword s v hv
  obtain ⟨hdom, _, hmem⟩ := R13Shards.panMemStoresHOL_word_spec
    (by simpa only [flattenHOL] using hst)
  have hslot : locN s "slot" = x.toNat := by
    have hlu : s.locals.lookup (ofString "slot") = some (.val (.word x)) := hx
    simp only [locN, hlu]
  have hr := logPointers_store_bo40 hp.1.1 hp.1.1.1.2.2 hp.1.2.1 hdom
    (by simpa only [hslot] using hp.1.2.2) hmem
  exact ⟨hr, hp.2.1, hr.1.2.2, hp.2.2⟩

theorem hoare_logPointers_increment :
    Hoare Phase4LogPointersReady
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))
      (fun r t => r = none → Phase4LogPointersReady t) := by
  apply Hoare.assign
  · intro F s v hp _ _
    exact LocalsOnly.setVar localsOnly_phase4LogPointersReady (by decide) v s hp
  · intro F s _ hr
    cases hr

theorem hoare_logSlot_store_increment (src : ExpHOL 64)
    (hword : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
      evalAt s src = some v → ∃ w : HolWordLab 64, v = .val w) :
    Hoare Phase4LogSlotReady
      (.seq (.store (.var .local (ofString "slot")) src)
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))
      (fun r t => r = none → Phase4LogPointersReady t) :=
  Hoare.seq_fall (hoare_logSlot_store src hword) hoare_logPointers_increment

def phase4LogCopySrc : ExpHOL 64 :=
  .load .one (.op .add [.var .local (ofString "lp"),
    .panop .mul [.var .local (ofString "i"), .const 8]])

def phase4LogCopyBody : ProgHOL 64 :=
  .decCall (ofString "slot") .one (ofString "lst_push")
    [.load .one (.op .add [.var .global (ofString "bo"), .const 40]), .const 8]
    (.seq (.store (.var .local (ofString "slot")) phase4LogCopySrc)
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))

theorem phase4LogCopySrc_word {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (he : evalAt s phase4LogCopySrc = some v) : ∃ w : HolWordLab 64, v = .val w := by
  unfold phase4LogCopySrc at he
  simp only [evalAt, evalHOLExact] at he
  split at he
  · rename_i ha
    split at he
    · rename_i hw
      simp only [memLoadHOLExact] at he
      split at he
      · cases he
        exact ⟨_, rfl⟩
      · cases he
    · cases he
  · cases he

/-- The log-push body preserves typed operands for subsequent stable allocation. -/
theorem hoare_phase4LogCopyBody_typed
    (hresume : DecCallResumeOn Phase4TypedLogPointers
      (fun s => Phase4LogSlotReady s ∧
        (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
        ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p)))
      (ofString "slot") (ofString "lst_push")
      [.load .one (.op .add [.var .global (ofString "bo"), .const 40]), .const 8]) :
    Hoare Phase4TypedLogPointers phase4LogCopyBody
      (fun r t => r = none → Phase4TypedLogPointers t) := by
  apply Hoare.decCall_fall (R := fun s => Phase4LogSlotReady s ∧
    (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
    ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p)))
    (by decide) localsOnly_phase4TypedLogPointers hresume
  refine Hoare.seq_fall (hoare_logSlot_store_typed phase4LogCopySrc phase4LogCopySrc_word) ?_
  apply Hoare.assign
  · intro F s v hp _ _
    exact LocalsOnly.setVar localsOnly_phase4TypedLogPointers (by decide) v s hp
  · intro F s _ hr
    cases hr

/-- The full log-push loop retains the typed stable-allocation operands. -/
theorem hoare_phase4LogCopyLoop_typed
    (hresume : DecCallResumeOn Phase4TypedLogPointers
      (fun s => Phase4LogSlotReady s ∧
        (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
        ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p)))
      (ofString "slot") (ofString "lst_push")
      [.load .one (.op .add [.var .global (ofString "bo"), .const 40]), .const 8]) :
    Hoare Phase4TypedLogPointers
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl")))
        phase4LogCopyBody)
      (fun r t => r = none → Phase4TypedLogPointers t) := by
  exact hoare_while_less_localsOnly localsOnly_phase4TypedLogPointers _ _
    (hoare_phase4LogCopyBody_typed hresume)
    (by unfold phase4LogCopyBody; ptx_incr) (by decide)

theorem hoare_phase4LogCopyBody
    (hresume : DecCallResumeOn Phase4LogPointersReady Phase4LogSlotReady
      (ofString "slot") (ofString "lst_push")
      [.load .one (.op .add [.var .global (ofString "bo"), .const 40]), .const 8]) :
    Hoare Phase4LogPointersReady phase4LogCopyBody
      (fun r t => r = none → Phase4LogPointersReady t) := by
  exact Hoare.decCall_fall (by decide) localsOnly_phase4LogPointersReady hresume
    (hoare_logSlot_store_increment phase4LogCopySrc phase4LogCopySrc_word)

theorem phase4LogCopyLoop_bound (h : PtxCallees)
    (hresume : DecCallResumeOn Phase4LogPointersReady Phase4LogSlotReady
      (ofString "slot") (ofString "lst_push")
      [.load .one (.op .add [.var .global (ofString "bo"), .const 40]), .const 8]) :
    TerminatingProgBoundedOn Phase4LogPointersReady
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl")))
        phase4LogCopyBody) ((2 ^ 64 + 1) * ((K.lst_push + 1) + 1)) := by
  apply while_less_localsOnly localsOnly_phase4LogPointersReady
  · unfold phase4LogCopyBody
    have hb : TerminatingProgBoundedOn Phase4LogPointersReady phase4LogCopyBody
        (K.lst_push + (0 + 0) + 1) := TerminatingProgBoundedOn.decCall_on h.fb_lst_push
      (ofString "slot") ShapeHOL.one
      [.load .one (.op .add [.var .global (ofString "bo"), .const 40]), .const 8]
      (P := Phase4LogPointersReady) (Q := Phase4LogSlotReady)
      (by intro F s vs body callee ret hc hp ha hl
          exact guestInv_callEntry s callee hp.1.1.1.1.1.1.1)
      hresume
      (seq_bound_trans
        (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
        (hoare_logSlot_store phase4LogCopySrc phase4LogCopySrc_word)
        (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s .local _ _)))
    intro F s hc hp
    simpa only [phase4LogCopyBody, Nat.zero_add, Nat.add_zero] using hb s hc hp
  · exact hoare_phase4LogCopyBody hresume
  · unfold phase4LogCopyBody
    ptx_incr

theorem phase4LogCopyLoop_typed_bound (h : PtxCallees)
    (hresume : DecCallResumeOn Phase4TypedLogPointers
      (fun s => Phase4LogSlotReady s ∧
        (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
        ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p)))
      (ofString "slot") (ofString "lst_push")
      [.load .one (.op .add [.var .global (ofString "bo"), .const 40]), .const 8]) :
    TerminatingProgBoundedOn Phase4TypedLogPointers
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl")))
        phase4LogCopyBody) ((2 ^ 64 + 1) * ((K.lst_push + 1) + 1)) := by
  apply while_less_localsOnly localsOnly_phase4TypedLogPointers
  · have hb : TerminatingProgBoundedOn Phase4TypedLogPointers phase4LogCopyBody
        (K.lst_push + (0 + 0) + 1) := TerminatingProgBoundedOn.decCall_on h.fb_lst_push
      (ofString "slot") ShapeHOL.one
      [.load .one (.op .add [.var .global (ofString "bo"), .const 40]), .const 8]
      (Bc := 0 + 0)
      (continuation := .seq (.store (.var .local (ofString "slot")) phase4LogCopySrc)
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))
      (P := Phase4TypedLogPointers)
      (Q := fun s => Phase4LogSlotReady s ∧
        (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
        ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p)))
      (by intro F s vs body callee ret hc hp ha hl
          exact guestInv_callEntry s callee hp.1.1.1.1.1.1.1.1)
      hresume
      (by
        intro F t hc ht
        exact seq_bound_trans
          (P := fun s => Phase4LogSlotReady s ∧
            (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
            ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p)))
          (by
            intro G u _ _ _
            have hu := clock_store u (.var .local (ofString "slot")) phase4LogCopySrc
            exact ⟨by omega, by omega⟩)
          (hoare_logSlot_store_typed phase4LogCopySrc phase4LogCopySrc_word)
          (by
            intro G u _ _ _
            have hu := clock_assign u .local (ofString "i")
              (.op .add [.var .local (ofString "i"), .const 1])
            exact ⟨by omega, by omega⟩) t hc ht)
    intro F s hc hp
    simpa only [Nat.zero_add, Nat.add_zero] using hb s hc hp
  · exact hoare_phase4LogCopyBody_typed hresume
  · unfold phase4LogCopyBody
    ptx_incr

/-- Compose the typed log-push loop with its stable-allocation continuation. -/
theorem phase4LogCopyLoop_typed_cut (h : PtxCallees)
    (hresume : DecCallResumeOn Phase4TypedLogPointers
      (fun s => Phase4LogSlotReady s ∧
        (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
        ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p)))
      (ofString "slot") (ofString "lst_push")
      [.load .one (.op .add [.var .global (ofString "bo"), .const 40]), .const 8])
    {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn Phase4TypedLogPointers tail b) :
    TerminatingProgBoundedOn Phase4TypedLogPointers
      (spinePlug 1 (spineAt 129 ptxCode) tail)
      ((2 ^ 64 + 1) * ((K.lst_push + 1) + 1) + b) := by
  have hb := @seq_bound_trans _ _ _ _ _ _ (phase4LogCopyLoop_typed_bound h hresume)
    (hoare_phase4LogCopyLoop_typed hresume) htail
  unfold ptxCode
  intro F s hc hp
  exact hb s hc hp

theorem phase4LogCopyLoop_cut (h : PtxCallees)
    (hresume : DecCallResumeOn Phase4LogPointersReady Phase4LogSlotReady
      (ofString "slot") (ofString "lst_push")
      [.load .one (.op .add [.var .global (ofString "bo"), .const 40]), .const 8])
    {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn Phase4LogPointersReady tail b) :
    TerminatingProgBoundedOn Phase4LogPointersReady
      (spinePlug 1 (spineAt 129 ptxCode) tail)
      ((2 ^ 64 + 1) * ((K.lst_push + 1) + 1) + b) := by
  have hp : Hoare Phase4LogPointersReady
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl")))
        phase4LogCopyBody) (fun r t => r = none → Phase4LogPointersReady t) :=
    hoare_while_less_localsOnly localsOnly_phase4LogPointersReady _ _
      (hoare_phase4LogCopyBody hresume)
      (by unfold phase4LogCopyBody; ptx_incr) (by decide)
  have hb := @seq_bound_trans _ _ _ _ _ _ (phase4LogCopyLoop_bound h hresume) hp htail
  unfold ptxCode
  intro F s hc hs
  exact hb s hc hs

theorem phase4LogCounter_typed_cut {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn Phase4TypedLogPointers tail b) :
    TerminatingProgBoundedOn Phase4TypedLogPointers
      (spinePlug 1 (spineAt 128 ptxCode) tail) b := by
  have hi : Hoare Phase4TypedLogPointers
      (.assign .local (ofString "i") (.const 0))
      (fun r t => r = none → Phase4TypedLogPointers t) := by
    apply Hoare.assign
    · intro F s v hp _ _
      exact LocalsOnly.setVar localsOnly_phase4TypedLogPointers (by decide) v s hp
    · intro F s _ hr
      cases hr
  unfold ptxCode
  intro F s hc hp
  rw [← Nat.zero_add b]
  refine seq_bound_trans ?_ hi htail s hc hp
  intro G t _ _ _
  have ht := clock_assign t .local (ofString "i") (.const 0)
  exact ⟨by omega, by omega⟩

theorem phase4LogCounter_cut {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn
      (fun s => Phase4LogPointersReady s ∧ locN s "i" = 0) tail b) :
    TerminatingProgBoundedOn Phase4LogPointersReady
      (spinePlug 1 (spineAt 128 ptxCode) tail) b := by
  have hb : TerminatingProgBoundedOn Phase4LogPointersReady
      (spinePlug 1 (spineAt 128 ptxCode) tail) (0 + b) := by
    unfold ptxCode
    refine seq_bound_trans (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s .local _ _))
      (Hoare.assign ?_ (fun _ _ hr => absurd hr (by simp))) htail
    intro F s v hp he _
    have hv : v = .val (.word (0 : BitVec 64)) := by
      change some (.val (.word (0 : BitVec 64))) = some v at he
      exact (Option.some.inj he).symm
    subst v
    refine ⟨LocalsOnly.setVar localsOnly_phase4LogPointersReady (by decide) _ s hp, ?_⟩
    change locN (setVarHOLFinite (ofString "i") (.val (.word (0 : BitVec 64))) s) "i" = 0
    simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  intro F s hc hp
  simpa only [Nat.zero_add] using hb s hc hp

theorem phase4ThroughLogCopy_cut (h : PtxCallees)
    (hresume : DecCallResumeOn Phase4LogPointersReady Phase4LogSlotReady
      (ofString "slot") (ofString "lst_push")
      [.load .one (.op .add [.var .global (ofString "bo"), .const 40]), .const 8])
    {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn Phase4LogPointersReady tail b) :
    TerminatingProgBoundedOn TxAfterCallStrong
      (spinePlug 31 (spineAt 99 ptxCode) tail)
      (phase4CreditCost + (K.max + 1) + ((K.lst_new + 1) +
        (K.encode_receipt + ((2 ^ 64 + 1) * ((K.lst_push + 1) + 1) + b) + 1))) := by
  have hloop := @phase4LogCopyLoop_cut h hresume _ _ htail
  have hcounter := @phase4LogCounter_cut _ _
    (bound_mono (Q := fun s => Phase4LogPointersReady s ∧ locN s "i" = 0)
      hloop (fun s hp => hp.1))
  have hb := @phase4ThroughLogPointers_cut h _ _ hcounter
  have he : spinePlug 31 (spineAt 99 ptxCode) tail =
      spinePlug 29 (spineAt 99 ptxCode)
        (spinePlug 1 (spineAt 128 ptxCode)
          (spinePlug 1 (spineAt 129 ptxCode) tail)) := by
    unfold ptxCode
    rfl
  rw [he]
  intro F s hc hp
  exact hb s hc hp

def Phase4StableCapInit : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => Phase4LogPointersReady s ∧ locN s "stable_log_cap" = locN s "nl"

theorem phase4StableCap_init {F : Type} (s : PanSemStateFiniteExact 64 F)
    (v : ValueHOL 64) (hp : Phase4LogPointersReady s)
    (he : evalAt s (.var .local (ofString "nl")) = some v) :
    Phase4StableCapInit (setVarHOLFinite (ofString "stable_log_cap") v s) := by
  refine ⟨LocalsOnly.setVar localsOnly_phase4LogPointersReady (by decide) v s hp, ?_⟩
  have hlu : s.locals.lookup (ofString "nl") = some v := he
  simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hlu,
    show ofString "stable_log_cap" ≠ ofString "nl" from by decide]

/-- Capacity initialization and adjustment preserve both typed copy operands. -/
theorem stable_capacity_copy_operands {F : Type} (s : PanSemStateFiniteExact 64 F)
    (v : ValueHOL 64)
    (hn : ∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n)))
    (hp : ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p))) :
    let t := setVarHOLFinite (ofString "stable_log_cap") v s
    (∃ n : BitVec 64, t.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
    (∃ p : BitVec 64, t.locals.lookup (ofString "lp") = some (.val (.word p))) := by
  simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
    show ofString "stable_log_cap" ≠ ofString "nl" by decide,
    show ofString "stable_log_cap" ≠ ofString "lp" by decide] using And.intro hn hp

/-- Initializing capacity from the length preserves the typed allocation operands. -/
theorem hoare_stable_capacity_init_copy :
    Hoare (fun s => Phase4LogPointersReady s ∧
      (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
      locN s "logs" ≠ 0 ∧
      ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p)))
      (.assign .local (ofString "stable_log_cap") (.var .local (ofString "nl")))
      (fun r t => r = none → Phase4StableCapInit t ∧
        (∃ n : BitVec 64, t.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
        locN t "logs" ≠ 0 ∧
        ∃ p : BitVec 64, t.locals.lookup (ofString "lp") = some (.val (.word p))) := by
  apply Hoare.assign
  · intro F s v hp he _
    obtain ⟨hn, hl⟩ := stable_capacity_copy_operands s v hp.2.1 hp.2.2.2
    refine ⟨phase4StableCap_init s v hp.1 he, hn, ?_, hl⟩
    simpa [locN, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "stable_log_cap" ≠ ofString "logs" by decide] using hp.2.2.1
  · intro F s hp hr
    cases hr

def Phase4StableCapReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => Phase4LogPointersReady s ∧
    locN s "stable_log_cap" = max 1 (locN s "nl")

theorem phase4StableCap_bounds {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : Phase4StableCapReady s) :
    1 ≤ locN s "stable_log_cap" ∧ locN s "nl" ≤ locN s "stable_log_cap" ∧
      8 * locN s "stable_log_cap" < 2 ^ 64 := by
  have hn := hp.1.1.2.1
  have hb := hp.1.1.1.2.2.1
  rw [hp.2]
  omega

/-- Capacity adjustment frames the typed copy operands and nonzero source. -/
theorem hoare_stable_capacity_frame :
    Hoare (fun s => (∃ n : BitVec 64,
      s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
      locN s "logs" ≠ 0 ∧ ∃ p : BitVec 64,
      s.locals.lookup (ofString "lp") = some (.val (.word p)))
      (.ite (.cmp .equal (.var .local (ofString "stable_log_cap")) (.const 0))
        (.assign .local (ofString "stable_log_cap") (.const 1)) .skip)
      (fun r t => r = none → (∃ n : BitVec 64,
        t.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
        locN t "logs" ≠ 0 ∧ ∃ p : BitVec 64,
        t.locals.lookup (ofString "lp") = some (.val (.word p))) := by
  apply Hoare.ite
  · apply Hoare.assign
    · intro F s v hp he _
      obtain ⟨hn, hz, hl⟩ := hp.1
      obtain ⟨hn', hl'⟩ := stable_capacity_copy_operands s v hn hl
      refine ⟨hn', ?_, hl'⟩
      simpa [locN, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
        show ofString "stable_log_cap" ≠ ofString "logs" by decide] using hz
    · intro F s hp hr
      cases hr
  · apply Hoare.skip
    intro F s hp _
    exact hp.1
  · intro F s hp hr
    cases hr

theorem hoare_phase4StableCap_adjust :
    Hoare Phase4StableCapInit
      (.ite (.cmp .equal (.var .local (ofString "stable_log_cap")) (.const 0))
        (.assign .local (ofString "stable_log_cap") (.const 1)) .skip)
      (fun r t => r = none → Phase4StableCapReady t) := by
  apply Hoare.ite
  · apply Hoare.assign
    · intro F s v hp he _
      obtain ⟨w, hw, hn⟩ := hp.2
      obtain ⟨a, b, ha, hb, hc⟩ := evalAt_cmp s .equal _ _ w hw
      have hb0 : b = 0 := by cases hb; rfl
      subst b
      have ha0 : a = 0 := by
        by_contra h
        have hz : (0 : BitVec 64) = 0#64 := rfl
        have h' : a ≠ 0#64 := h
        simp [wordCmpHOL] at hc
        rw [if_neg h'] at hc
        exact hn hc
      have hz : locN s "stable_log_cap" = 0 := by
        change s.locals.lookup _ = some (.val (.word a)) at ha
        simp [locN, ha, ha0]
      have hv : v = .val (.word (1 : BitVec 64)) := by cases he; rfl
      subst v
      refine ⟨LocalsOnly.setVar localsOnly_phase4LogPointersReady (by decide) _ s hp.1.1, ?_⟩
      have hn0 : locN s "nl" = 0 := hp.1.2.symm.trans hz
      simp [locN, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
        show ofString "stable_log_cap" ≠ ofString "nl" from by decide] at hn0 ⊢
      rw [hn0]
      decide
    · intro F s hp hr
      cases hr
  · apply Hoare.skip
    intro F s hp _
    obtain ⟨a, b, ha, hb, hc⟩ := evalAt_cmp s .equal _ _ 0 hp.2
    have hb0 : b = 0 := by cases hb; rfl
    subst b
    have ha0 : a ≠ 0 := by
      intro h
      simp [wordCmpHOL, h] at hc
    have hz : locN s "stable_log_cap" ≠ 0 := by
      change s.locals.lookup _ = some (.val (.word a)) at ha
      intro hz
      apply ha0
      apply BitVec.eq_of_toNat_eq
      simpa [locN, ha] using hz
    refine ⟨hp.1.1, ?_⟩
    have he := hp.1.2
    omega
  · intro F s hp hr
    cases hr

/-- Capacity adjustment establishes the allocation precondition with typed operands. -/
theorem hoare_phase4StableCap_copy_ready :
    Hoare (fun s => Phase4StableCapInit s ∧
      (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
      locN s "logs" ≠ 0 ∧
      ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p)))
      (.ite (.cmp .equal (.var .local (ofString "stable_log_cap")) (.const 0))
        (.assign .local (ofString "stable_log_cap") (.const 1)) .skip)
      (fun r t => r = none → Phase4StableCapReady t ∧
        (∃ n : BitVec 64, t.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
        locN t "logs" ≠ 0 ∧
        ∃ p : BitVec 64, t.locals.lookup (ofString "lp") = some (.val (.word p))) := by
  constructor
  intro F s hc hp hnt hr
  exact ⟨hoare_phase4StableCap_adjust.run s hc hp.1 hnt hr,
    hoare_stable_capacity_frame.run s hc hp.2 hnt hr⟩

/-- Capacity normalization adds no clock cost before a fully typed allocation tail. -/
theorem stable_capacity_copy_cut {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn (fun s => Phase4StableCapReady s ∧
      (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
      locN s "logs" ≠ 0 ∧
      ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p))) tail b) :
    TerminatingProgBoundedOn (fun s => Phase4StableCapInit s ∧
      (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
      locN s "logs" ≠ 0 ∧
      ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p)))
      (.seq (.ite (.cmp .equal (.var .local (ofString "stable_log_cap")) (.const 0))
        (.assign .local (ofString "stable_log_cap") (.const 1)) .skip) tail) b := by
  intro F s hc hp
  rw [← Nat.zero_add b]
  refine seq_bound_trans ?_ hoare_phase4StableCap_copy_ready htail s hc hp
  intro G t hcode hpre
  exact TerminatingProgBoundedOn.ite_on
    (yes := .assign .local (ofString "stable_log_cap") (.const 1)) (no := .skip)
    (a := 0) (b := 0)
    (P := fun u => Phase4StableCapInit u ∧
    (∃ n : BitVec 64, u.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
    locN u "logs" ≠ 0 ∧
    ∃ p : BitVec 64, u.locals.lookup (ofString "lp") = some (.val (.word p)))
    (fun u _ _ _ => by
      have hu := clock_assign u .local (ofString "stable_log_cap") (.const 1)
      exact ⟨by omega, by omega⟩)
    (fun u _ _ _ => by
      have hu := clock_skip u
      exact ⟨by omega, by omega⟩) t hcode hpre

/-- The concrete capacity declaration and adjustment retain copy operands. -/
theorem stable_capacity_setup_copy_cut {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn (fun s => Phase4StableCapReady s ∧
      (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
      locN s "logs" ≠ 0 ∧
      ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p))) tail b) :
    TerminatingProgBoundedOn (fun s => Phase4LogPointersReady s ∧
      (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
      locN s "logs" ≠ 0 ∧
      ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p)))
      (spinePlug 2 (spineAt 130 ptxCode) tail) b := by
  unfold ptxCode
  intro F t hc ht
  refine dec_bound_trans (P := fun s => Phase4LogPointersReady s ∧
    (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
    locN s "logs" ≠ 0 ∧
    ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p)))
    ?_ (stable_capacity_copy_cut htail) t hc ht
  intro F s v hp he
  obtain ⟨hn, hl⟩ := stable_capacity_copy_operands s v hp.2.1 hp.2.2.2
  refine ⟨phase4StableCap_init s v hp.1 he, hn, ?_, hl⟩
  simpa [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
    show ofString "stable_log_cap" ≠ ofString "logs" by decide] using hp.2.2.1

/-- Source loads, log pushing, and capacity setup form one concrete prefix. -/
theorem phase4Logs_capacity_typed_cut (h : PtxCallees)
    (hresume : DecCallResumeOn Phase4TypedLogPointers
      (fun s => Phase4LogSlotReady s ∧
        (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
        ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p)))
      (ofString "slot") (ofString "lst_push")
      [.load .one (.op .add [.var .global (ofString "bo"), .const 40]), .const 8])
    {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn (fun s => Phase4StableCapReady s ∧
      (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
      locN s "logs" ≠ 0 ∧
      ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p))) tail b) :
    TerminatingProgBoundedOn Phase4ReceiptEncoded
      (spinePlug 6 (spineAt 126 ptxCode) tail)
      ((2 ^ 64 + 1) * ((K.lst_push + 1) + 1) + b) := by
  have hc := @stable_capacity_setup_copy_cut _ _ htail
  have hl := @phase4LogCopyLoop_typed_cut h hresume _ _ hc
  have hi := @phase4LogCounter_typed_cut _ _ hl
  have hb := @phase4LogPointers_copy_cut _ _ hi
  have he : spinePlug 6 (spineAt 126 ptxCode) tail =
      spinePlug 2 (spineAt 126 ptxCode)
        (spinePlug 1 (spineAt 128 ptxCode)
          (spinePlug 1 (spineAt 129 ptxCode)
            (spinePlug 2 (spineAt 130 ptxCode) tail))) := by
    unfold ptxCode
    rfl
  rw [he]
  intro F s hcode hp
  exact hb s hcode hp

/-- The receipt prefix reaches stable allocation with all copy operands retained. -/
theorem phase4ThroughCapacity_typed_cut (h : PtxCallees)
    (hresume : DecCallResumeOn Phase4TypedLogPointers
      (fun s => Phase4LogSlotReady s ∧
        (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
        ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p)))
      (ofString "slot") (ofString "lst_push")
      [.load .one (.op .add [.var .global (ofString "bo"), .const 40]), .const 8])
    {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn (fun s => Phase4StableCapReady s ∧
      (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
      locN s "logs" ≠ 0 ∧
      ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p))) tail b) :
    TerminatingProgBoundedOn TxAfterCallStrong
      (spinePlug 33 (spineAt 99 ptxCode) tail)
      (phase4CreditCost + (K.max + 1) + ((K.lst_new + 1) +
        (K.encode_receipt + ((2 ^ 64 + 1) * ((K.lst_push + 1) + 1) + b) + 1))) := by
  have hb := @phase4ThroughReceiptStores_cut h _ _
    (phase4Logs_capacity_typed_cut h hresume htail)
  have he : spinePlug 33 (spineAt 99 ptxCode) tail =
      spinePlug 27 (spineAt 99 ptxCode) (spinePlug 6 (spineAt 126 ptxCode) tail) := by
    unfold ptxCode
    rfl
  rw [he]
  intro F s hc hp
  exact hb s hc hp

theorem phase4StableCap_cut {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn Phase4StableCapReady tail b) :
    TerminatingProgBoundedOn Phase4LogPointersReady
      (spinePlug 2 (spineAt 130 ptxCode) tail) b := by
  have hb : TerminatingProgBoundedOn Phase4LogPointersReady
      (spinePlug 2 (spineAt 130 ptxCode) tail) (0 + b) := by
    unfold ptxCode
    refine dec_bound_trans (fun s v hp he => phase4StableCap_init s v hp he) ?_
    refine seq_bound_trans ?_ hoare_phase4StableCap_adjust htail
    exact TerminatingProgBoundedOn.ite_on
      (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s .local _ _))
      (TerminatingProgBoundedOn.of_clock clock_skip)
  intro F s hc hp
  simpa only [Nat.zero_add] using hb s hc hp

theorem lst_new_stable_args {F : Type} (s : PanSemStateFiniteExact 64 F)
    (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret)) :
    let ent := callEntryStateHOLFinite s callee
    locN ent "esz" = 8 ∧ locN ent "cap" = locN s "stable_log_cap" ∧
      1 ≤ locN ent "cap" ∧ locN ent "esz" * locN ent "cap" < 2 ^ 64 := by
  have ha' := ha
  rw [evalListHOLFinite_eq_toExact] at ha'
  cases hv : s.locals.lookup (ofString "stable_log_cap") with
  | none => simp [evalListHOLExact, evalHOLExact, hv] at ha'
  | some v =>
    have hlc := R13Shards.lookup_lst_new
    rw [← hc] at hlc
    obtain ⟨_, he, hcap⟩ := callee_param_two_exp s (ofString "lst_new")
      (ofString "esz") (ofString "cap") .one .one _ _ hlc
      (.const 8) (.var .local (ofString "stable_log_cap")) (.val (.word 8)) v
      vs body callee ret rfl hv ha hl
    have he8 : locN (callEntryStateHOLFinite s callee) "esz" = 8 := by
      simp [locN, callEntryStateHOLFinite, he]
    have hce : locN (callEntryStateHOLFinite s callee) "cap" = locN s "stable_log_cap" := by
      simp [locN, callEntryStateHOLFinite, hcap, hv]
    have hb := phase4StableCap_bounds s hp
    exact ⟨he8, hce, hce.symm ▸ hb.1, by rw [he8, hce]; exact hb.2.2⟩

theorem lst_new_stable_fresh (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    ∃ w : BitVec 64, v = .val (.word w) ∧
      FreshBlock (callEntryStateHOLFinite s callee) post w.toNat 24 ∧
      FreshBlock (callEntryStateHOLFinite s callee) post (memW post w.toNat)
        (8 * locN s "stable_log_cap") ∧ memW post (w.toNat + 8) = 0 ∧
      ∃ S Nd, WorldTypedWith post S Nd ∧
        IvlsDisj [(w.toNat, 24), (memW post w.toNat, 8 * locN s "stable_log_cap")]
          (worldOwned post S Nd) := by
  have hargs := lst_new_stable_args s vs body callee ret hc hp ha hl
  have hW := hp.1.1.1.1.1.1
  have hw := funSpec_at_lookup h.wk_lst_new s hc vs body callee ret hl
    (worldOK_callEntry hW callee) (by rw [hr]; simp)
  rw [hr] at hw
  have hs := hw (Or.inl ⟨v, rfl⟩)
  obtain ⟨S, hWT⟩ := hW.2
  obtain ⟨Nd, hTr⟩ := hWT.2.2.2
  have hWTc := (R13Shards.worldTypedWith_with_locals s callee (s.clock - 1) S Nd).mpr
    ⟨hWT.1, hWT.2.1, hWT.2.2.1, hTr⟩
  obtain ⟨S', Nd', _, hWT', _, _, hret⟩ := hs.2.2.2.2 S Nd hWTc
    (by intro i hi; cases hi)
  obtain ⟨w, hv, hd⟩ := hret hargs.2.2.2 v rfl
  have ht := funSpec_at_lookup h.rt_lst_new s hc vs body callee ret hl
    (worldOK_callEntry hW callee).1 (by rw [hr]; simp)
  rw [hr] at ht
  obtain ⟨w', hv', _, _, hf⟩ := ht v rfl
  have heq : w' = w := by rw [hv] at hv'; cases hv'; rfl
  subst w'
  obtain ⟨hh, hb, _, hn, _⟩ := hf hargs.2.2.2 hargs.2.2.1
  refine ⟨w, hv, hh, ?_, hn, S', Nd', hWT', ?_⟩
  · simpa only [hargs.1, hargs.2.1] using hb
  · simpa only [hargs.1, hargs.2.1] using hd

/-- The allocator separates its returned header from its backing region. -/
theorem lst_new_stable_resumed_header_backing (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    let t := setVarHOLFinite (ofString "stable_logs") v {post with locals := s.locals}
    Disj (locN t "stable_logs", 24)
      (memW t (locN t "stable_logs"), 8 * locN t "stable_log_cap") := by
  have hargs := lst_new_stable_args s vs body callee ret hc hp ha hl
  have ht := funSpec_at_lookup h.rt_lst_new s hc vs body callee ret hl
    (worldOK_callEntry hp.1.1.1.1.1.1 callee).1 (by rw [hr]; simp)
  rw [hr] at ht
  obtain ⟨w, rfl, _, _, hf⟩ := ht v rfl
  have hd := (hf hargs.2.2.2 hargs.2.2.1).2.2.1
  rw [hargs.1, hargs.2.1] at hd
  simpa [locN, memW, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
    show ofString "stable_logs" ≠ ofString "stable_log_cap" by decide] using hd

/-- Fresh header allocation establishes the allocation premise of the length store. -/
theorem lst_new_stable_header_allocated (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    let t := setVarHOLFinite (ofString "stable_logs") v {post with locals := s.locals}
    Allocated t (locN t "stable_logs", 24) := by
  obtain ⟨w, rfl, hh, _⟩ := lst_new_stable_fresh h s vs body callee ret v post hc hp ha hl hr
  have hbase := hp.1.1.1.1.1.1.1.2.1
  have hi := hh.2.1
  apply Or.inl
  simpa [Inside, locN, globN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
    callEntryStateHOLFinite] using
    (show sourceBase ≤ w.toNat ∧ w.toNat + 24 ≤ globN post "heap_ptr" from
      ⟨hbase.trans hi.1, hi.2⟩)

theorem lst_new_stable_source_resume (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    Phase4StableCapReady (setVarHOLFinite (ofString "stable_logs") v
      {post with locals := s.locals}) := by
  have hw := funSpec_at_lookup h.wk_lst_new s hc vs body callee ret hl
    (worldOK_callEntry hp.1.1.1.1.1.1 callee) (by rw [hr]; simp)
  rw [hr] at hw
  have hs := hw (Or.inl ⟨v, rfl⟩)
  have hs' := R13Shards.worldStep_with_locals hs s.locals s.clock
  have hp' := logPointers_heapStep hs' hp.1 hp.1.1.2.2
  refine ⟨LocalsOnly.setVar localsOnly_phase4LogPointersReady (by decide) v _ hp', ?_⟩
  simpa [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
    show ofString "stable_logs" ≠ ofString "stable_log_cap" from by decide,
    show ofString "stable_logs" ≠ ofString "nl" from by decide] using hp.2

theorem lst_new_stable_capacity (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    ∃ w : BitVec 64, v = .val (.word w) ∧
      memW post (w.toNat + 16) = locN s "stable_log_cap" := by
  have hargs := lst_new_stable_args s vs body callee ret hc hp ha hl
  have ht := funSpec_at_lookup h.rt_lst_new s hc vs body callee ret hl
    (worldOK_callEntry hp.1.1.1.1.1.1 callee).1 (by rw [hr]; simp)
  rw [hr] at ht
  obtain ⟨w, hv, _, _, hf⟩ := ht v rfl
  obtain ⟨_, _, _, _, hcap⟩ := hf hargs.2.2.2 hargs.2.2.1
  exact ⟨w, hv, hcap.trans hargs.2.1⟩

theorem fresh_empty_stable_logs {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {logs cap : Nat} (hA : ArenaOK s)
    (hh : FreshBlock s post logs 24)
    (hb : FreshBlock s post (memW post logs) (8 * cap))
    (hd : IvlsDisj [(logs, 24), (memW post logs, 8 * cap)] (worldOwned post S Nd))
    (hn : memW post (logs + 8) = 0) :
    LogsListOK post logs ∧ LogsLiveOwned post S Nd logs ∧ LogsDisjFixed post logs := by
  have hhi : Inside (logs, 24) sourceBase (globN post "heap_ptr") := by
    have hi := hh.2.1
    change Inside (logs, 24) (globN s "heap_ptr") (globN post "heap_ptr") at hi
    exact ⟨hA.1.trans hi.1, hi.2⟩
  have hbi : Inside (memW post logs, 0) sourceBase (globN post "heap_ptr") := by
    have hi := hb.2.1
    constructor
    · exact hA.1.trans hi.1
    · have := hi.2; dsimp [Inside] at this ⊢; omega
  have ho := logsLiveOwned_empty (S := S) (Nd := Nd) (Or.inl hbi)
    (fun j hj => hd _ (by simp) j hj) hn
  exact ⟨logsListOK_empty hh.2.2 (Or.inl hhi) hn, ho, logsLiveOwned_disjFixed ho⟩

theorem lst_new_stable_owned (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    ∃ w : BitVec 64, v = .val (.word w) ∧ LogsListOK post w.toNat ∧
      LogsWorldOwned post w.toNat ∧ LogsDisjFixed post w.toNat := by
  obtain ⟨w, hv, hh, hb, hn, S, Nd, hw, hd⟩ :=
    lst_new_stable_fresh h s vs body callee ret v post hc hp ha hl hr
  have ho := fresh_empty_stable_logs
    (worldOK_callEntry hp.1.1.1.1.1.1 callee).1.2 hh hb hd hn
  exact ⟨w, hv, ho.1, ⟨S, Nd, hw, ho.2.1⟩, ho.2.2⟩

def Phase4StableAllocated : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => Phase4StableCapReady s ∧ LogsListOK s (locN s "stable_logs") ∧
    LogsWorldOwned s (locN s "stable_logs") ∧ LogsDisjFixed s (locN s "stable_logs")

theorem lst_new_stable_allocated_resume (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    Phase4StableAllocated (setVarHOLFinite (ofString "stable_logs") v
      {post with locals := s.locals}) := by
  have hp' := lst_new_stable_source_resume h s vs body callee ret v post hc hp hl hr
  obtain ⟨w, rfl, hlst, howned, hfixed⟩ :=
    lst_new_stable_owned h s vs body callee ret v post hc hp ha hl hr
  refine ⟨hp', ?_, ?_, ?_⟩
  all_goals simp only [locN, setVarHOLFinite, HolFiniteMapExact.lookup_update,
    if_pos rfl, valueWord, Option.getD]
  · exact hlst
  · exact logsWorldOwned_with_locals _ _ howned
  · exact hfixed

/-- Allocation preserves the source pointer and length cells, so source
separation can be transported to the resumed memory. -/
theorem lst_new_stable_source_cells (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    memW post (locN s "logs") = memW s (locN s "logs") ∧
    memW post (locN s "logs" + 8) = memW s (locN s "logs" + 8) := by
  have hp' := lst_new_stable_source_resume h s vs body callee ret v post hc hp hl hr
  have hlp := hp'.1.2
  have hnl := hp'.1.1.2.1
  simp only [locN, memW, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
    show ofString "stable_logs" ≠ ofString "lp" by decide,
    show ofString "stable_logs" ≠ ofString "logs" by decide,
    show ofString "stable_logs" ≠ ofString "nl" by decide, if_false] at hlp hnl
  exact ⟨hlp.symm.trans hp.1.2, hnl.symm.trans hp.1.1.2.1⟩

/-- The allocator leaves every source record pointer unchanged. -/
theorem lst_new_stable_source_entries (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    ∀ i, i < memW s (locN s "logs" + 8) →
      memW post (memW s (locN s "logs") + 8 * i) =
        memW s (memW s (locN s "logs") + 8 * i) := by
  have hw := funSpec_at_lookup h.wk_lst_new s hc vs body callee ret hl
    (worldOK_callEntry hp.1.1.1.1.1.1 callee) (by rw [hr]; simp)
  rw [hr] at hw
  have hs := R13Shards.worldStep_with_locals (hw (Or.inl ⟨v, rfl⟩)) s.locals s.clock
  obtain ⟨a, b, _, _, _, _, ho⟩ := hp.1.1.1.2.2.2
  exact logsWorldOwned_heapStep_array hs hp.1.1.1.1.1.1.1 hp.1.1.1.2.1 ho hp.1.1.2.2

theorem lst_new_stable_capacity_resume (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    let resumed := setVarHOLFinite (ofString "stable_logs") v {post with locals := s.locals}
    Phase4StableAllocated resumed ∧
      memW resumed (locN resumed "stable_logs" + 16) = locN resumed "stable_log_cap" := by
  refine ⟨lst_new_stable_allocated_resume h s vs body callee ret v post hc hp ha hl hr, ?_⟩
  obtain ⟨w, rfl, hw⟩ := lst_new_stable_capacity h s vs body callee ret v post hc hp ha hl hr
  simpa [locN, memW, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
    show ofString "stable_logs" ≠ ofString "stable_log_cap" from by decide] using hw

theorem stable_backing_allocated {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {p cap : Nat} (hA : ArenaOK s) (hb : FreshBlock s post p (8 * cap)) :
    p % 8 = 0 ∧ Allocated post (p, 8 * cap) ∧ WordsOK post (p, 8 * cap) := by
  have hround : (8 * cap + 7) / 8 * 8 = 8 * cap := by omega
  obtain ⟨halign, hi, hw⟩ := hb
  rw [hround] at hi hw
  exact ⟨halign, Or.inl ⟨hA.1.trans hi.1, hi.2⟩, hw⟩

theorem lst_new_stable_backing_resume (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    let resumed := setVarHOLFinite (ofString "stable_logs") v {post with locals := s.locals}
    let p := memW resumed (locN resumed "stable_logs")
    p % 8 = 0 ∧ Allocated resumed (p, 8 * locN resumed "stable_log_cap") ∧
      WordsOK resumed (p, 8 * locN resumed "stable_log_cap") := by
  obtain ⟨w, rfl, _, hb, _⟩ :=
    lst_new_stable_fresh h s vs body callee ret v post hc hp ha hl hr
  have hb' := stable_backing_allocated
    (worldOK_callEntry hp.1.1.1.1.1.1 callee).1.2 hb
  simpa [locN, memW, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
    Allocated, WordsOK, WordAt, globN,
    show ofString "stable_logs" ≠ ofString "stable_log_cap" from by decide] using hb'

def Phase4StableStorageReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => Phase4StableAllocated s ∧
    memW s (locN s "stable_logs" + 16) = locN s "stable_log_cap" ∧
    let p := memW s (locN s "stable_logs")
    p % 8 = 0 ∧ Allocated s (p, 8 * locN s "stable_log_cap") ∧
      WordsOK s (p, 8 * locN s "stable_log_cap")

theorem lst_new_stable_storage_resume (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    Phase4StableStorageReady (setVarHOLFinite (ofString "stable_logs") v
      {post with locals := s.locals}) := by
  obtain ⟨hp', hcap⟩ := lst_new_stable_capacity_resume h s vs body callee ret v post hc hp ha hl hr
  exact ⟨hp', hcap, lst_new_stable_backing_resume h s vs body callee ret v post hc hp ha hl hr⟩

theorem phase4StableAllocation_cut (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn Phase4StableStorageReady tail b) :
    TerminatingProgBoundedOn Phase4StableCapReady
      (spinePlug 1 (spineAt 132 ptxCode) tail) (K.lst_new + b + 1) := by
  unfold ptxCode
  refine TerminatingProgBoundedOn.decCall_on h.fb_lst_new _ _ _ ?_ ?_ htail
  · intro F s vs body callee ret hc hp ha hl
    exact guestInv_callEntry s callee hp.1.1.1.1.1.1.1.1
  · intro F s vs body callee ret v post hc hp ha hl hr
    exact lst_new_stable_storage_resume h s vs body callee ret v post hc hp ha hl hr

theorem phase4StableSetup_cut (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn Phase4StableStorageReady tail b) :
    TerminatingProgBoundedOn Phase4LogPointersReady
      (spinePlug 3 (spineAt 130 ptxCode) tail) (K.lst_new + b + 1) := by
  have hb := @phase4StableCap_cut _ _ (phase4StableAllocation_cut h htail)
  have he : spinePlug 3 (spineAt 130 ptxCode) tail =
      spinePlug 2 (spineAt 130 ptxCode)
        (spinePlug 1 (spineAt 132 ptxCode) tail) := by
    unfold ptxCode
    rfl
  rw [he]
  intro F s hc hp
  exact hb s hc hp

theorem phase4ThroughStableSetup_cut (h : PtxCallees)
    (hresume : DecCallResumeOn Phase4LogPointersReady Phase4LogSlotReady
      (ofString "slot") (ofString "lst_push")
      [.load .one (.op .add [.var .global (ofString "bo"), .const 40]), .const 8])
    {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn Phase4StableStorageReady tail b) :
    TerminatingProgBoundedOn TxAfterCallStrong
      (spinePlug 34 (spineAt 99 ptxCode) tail)
      (phase4CreditCost + (K.max + 1) + ((K.lst_new + 1) +
        (K.encode_receipt + ((2 ^ 64 + 1) * ((K.lst_push + 1) + 1) +
          (K.lst_new + b + 1)) + 1))) := by
  have hb := @phase4ThroughLogCopy_cut h hresume _ _ (phase4StableSetup_cut h htail)
  have he : spinePlug 34 (spineAt 99 ptxCode) tail =
      spinePlug 31 (spineAt 99 ptxCode) (spinePlug 3 (spineAt 130 ptxCode) tail) := by
    unfold ptxCode
    rfl
  rw [he]
  intro F s hc hp
  exact hb s hc hp

theorem stable_storage_length_fits {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : Phase4StableStorageReady s) :
    locN s "nl" ≤ memW s (locN s "stable_logs" + 16) ∧
      8 * locN s "nl" < 2 ^ 64 ∧
      ∀ i : Nat, i < locN s "nl" →
        WordAt s (memW s (locN s "stable_logs") + 8 * i) := by
  have hb := phase4StableCap_bounds s hp.1.1
  refine ⟨by rw [hp.2.1]; exact hb.2.1, ?_, ?_⟩
  · exact lt_of_le_of_lt (Nat.mul_le_mul_left 8 hb.2.1) hb.2.2
  · intro i hi
    have hw := hp.2.2.2.2
    apply hw.2.2 i
    have hic : i < locN s "stable_log_cap" := lt_of_lt_of_le hi hb.2.1
    simpa using hic

theorem lst_new_stable_header_resume (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    let resumed := setVarHOLFinite (ofString "stable_logs") v {post with locals := s.locals}
    WordsOK resumed (locN resumed "stable_logs", 24) ∧
      Allocated resumed (locN resumed "stable_logs", 24) := by
  obtain ⟨w, rfl, hh, _⟩ :=
    lst_new_stable_fresh h s vs body callee ret v post hc hp ha hl hr
  have hi : Inside (w.toNat, 24) sourceBase (globN post "heap_ptr") :=
    ⟨(worldOK_callEntry hp.1.1.1.1.1.1 callee).1.2.1.trans hh.2.1.1, hh.2.1.2⟩
  have hw : WordsOK post (w.toNat, 24) := hh.2.2
  have ho : Allocated post (w.toNat, 24) := Or.inl hi
  simpa [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
    Allocated, WordsOK, WordAt, globN] using And.intro hw ho

theorem stable_length_field_word {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hh : WordsOK s (locN s "stable_logs", 24)) :
    WordAt s (locN s "stable_logs" + 8) := by
  have hw := hh.2.2 1 (by norm_num)
  simpa using hw

theorem stable_length_address_bound {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hA : ArenaOK s) (hh : Allocated s (locN s "stable_logs", 24)) :
    locN s "stable_logs" + 8 < 2 ^ 64 ∧
      (BitVec.ofNat 64 (locN s "stable_logs") + (8 : BitVec 64)).toNat =
        locN s "stable_logs" + 8 := by
  have hb := (ivl_allocated_bound hA hh).2
  have hlt : locN s "stable_logs" + 8 < 2 ^ 64 := by dsimp at hb; omega
  refine ⟨hlt, ?_⟩
  have hl : locN s "stable_logs" < 2 ^ 64 := by omega
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hl, show (8 : BitVec 64).toNat = 8 from rfl,
    Nat.mod_eq_of_lt hlt]

theorem stable_length_store_value {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : Phase4StableStorageReady s)
    (mem' : BitVec 64 → HolWordLab 64)
    (hm : mem' (BitVec.ofNat 64 (locN s "stable_logs" + 8)) =
      .word (BitVec.ofNat 64 (locN s "nl"))) :
    memW {s with memory := mem'} (locN s "stable_logs" + 8) = locN s "nl" := by
  have hb := (stable_storage_length_fits s hp).2.1
  have hn : locN s "nl" < 2 ^ 64 := by omega
  change (valueWord (.val (mem' (BitVec.ofNat 64 (locN s "stable_logs" + 8))))).toNat = _
  rw [hm]
  exact Nat.mod_eq_of_lt hn

theorem stable_length_store_header_unchanged {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hA : ArenaOK s)
    (hh : Allocated s (locN s "stable_logs", 24))
    (mem' : BitVec 64 → HolWordLab 64)
    (hm : ∀ a, a ≠ BitVec.ofNat 64 (locN s "stable_logs" + 8) → mem' a = s.memory a) :
    memW {s with memory := mem'} (locN s "stable_logs") = memW s (locN s "stable_logs") ∧
    memW {s with memory := mem'} (locN s "stable_logs" + 16) =
      memW s (locN s "stable_logs" + 16) := by
  have hb := (ivl_allocated_bound hA hh).2
  have h0 : locN s "stable_logs" < 2 ^ 64 := by dsimp at hb; omega
  have h8 : locN s "stable_logs" + 8 < 2 ^ 64 := by dsimp at hb; omega
  have h16 : locN s "stable_logs" + 16 < 2 ^ 64 := by dsimp at hb; omega
  have hn0 : BitVec.ofNat 64 (locN s "stable_logs") ≠
      BitVec.ofNat 64 (locN s "stable_logs" + 8) := by
    intro he
    have he' := congrArg BitVec.toNat he
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h0, Nat.mod_eq_of_lt h8] at he'
    omega
  have hn16 : BitVec.ofNat 64 (locN s "stable_logs" + 16) ≠
      BitVec.ofNat 64 (locN s "stable_logs" + 8) := by
    intro he
    have he' := congrArg BitVec.toNat he
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h16, Nat.mod_eq_of_lt h8] at he'
    omega
  constructor <;> simp only [memW]
  · rw [hm _ hn0]
  · rw [hm _ hn16]

theorem stable_length_store_words {F : Type} (s : PanSemStateFiniteExact 64 F)
    (mem' : BitVec 64 → HolWordLab 64) (w : BitVec 64)
    (he : mem' (BitVec.ofNat 64 (locN s "stable_logs" + 8)) = .word w)
    (hm : ∀ a, a ≠ BitVec.ofNat 64 (locN s "stable_logs" + 8) → mem' a = s.memory a)
    {i : Ivl} (hi : WordsOK s i) : WordsOK {s with memory := mem'} i := by
  refine ⟨hi.1, hi.2.1, ?_⟩
  intro k hk
  obtain ⟨v, hd, hv⟩ := hi.2.2 k hk
  by_cases ha : BitVec.ofNat 64 (i.1 + 8 * k) =
      BitVec.ofNat 64 (locN s "stable_logs" + 8)
  · exact ⟨w, hd, by change mem' _ = _; rw [ha, he]⟩
  · exact ⟨v, hd, (hm _ ha).trans hv⟩

/-- A word-valued length write retains the allocated, readable stable header
needed by the subsequent backing-pointer load. -/
theorem stable_length_store_header_ready {F : Type} (s : PanSemStateFiniteExact 64 F)
    (mem' : BitVec 64 → HolWordLab 64) (w : BitVec 64)
    (he : mem' (BitVec.ofNat 64 (locN s "stable_logs" + 8)) = .word w)
    (hm : ∀ a, a ≠ BitVec.ofNat 64 (locN s "stable_logs" + 8) → mem' a = s.memory a)
    (hh : WordsOK s (locN s "stable_logs", 24))
    (ha : Allocated s (locN s "stable_logs", 24)) :
    let t := {s with memory := mem'}
    WordsOK t (locN t "stable_logs", 24) ∧
      Allocated t (locN t "stable_logs", 24) ∧ WordAt t (locN t "stable_logs") := by
  have hw := stable_length_store_words s mem' w he hm hh
  refine ⟨hw, ha, ?_⟩
  have h0 := hw.2.2 0 (by change 0 < 24 / 8; decide)
  simpa only [Nat.mul_zero, Nat.add_zero, locN] using h0

theorem stable_length_store_backing {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : Phase4StableStorageReady s) (hA : ArenaOK s)
    (hh : Allocated s (locN s "stable_logs", 24))
    (mem' : BitVec 64 → HolWordLab 64) (w : BitVec 64)
    (he : mem' (BitVec.ofNat 64 (locN s "stable_logs" + 8)) = .word w)
    (hm : ∀ a, a ≠ BitVec.ofNat 64 (locN s "stable_logs" + 8) → mem' a = s.memory a) :
    let post := {s with memory := mem'}
    Allocated post (memW post (locN post "stable_logs"), 8 * locN post "stable_log_cap") ∧
      WordsOK post (memW post (locN post "stable_logs"), 8 * locN post "stable_log_cap") := by
  have hptr := (stable_length_store_header_unchanged s hA hh mem' hm).1
  change Allocated {s with memory := mem'}
      (memW {s with memory := mem'} (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
    WordsOK {s with memory := mem'}
      (memW {s with memory := mem'} (locN s "stable_logs"), 8 * locN s "stable_log_cap")
  rw [hptr]
  exact ⟨hp.2.2.2.1, stable_length_store_words s mem' w he hm hp.2.2.2.2⟩

theorem stable_length_store_fits {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : Phase4StableStorageReady s) (hA : ArenaOK s)
    (hh : Allocated s (locN s "stable_logs", 24))
    (mem' : BitVec 64 → HolWordLab 64)
    (he : mem' (BitVec.ofNat 64 (locN s "stable_logs" + 8)) =
      .word (BitVec.ofNat 64 (locN s "nl")))
    (hm : ∀ a, a ≠ BitVec.ofNat 64 (locN s "stable_logs" + 8) → mem' a = s.memory a) :
    memW {s with memory := mem'} (locN s "stable_logs" + 8) ≤
      memW {s with memory := mem'} (locN s "stable_logs" + 16) := by
  rw [stable_length_store_value s hp mem' he,
    (stable_length_store_header_unchanged s hA hh mem' hm).2]
  exact (stable_storage_length_fits s hp).1

/-- A store separated from the source header, live array and records retains
both source-log validity and ownership under an unchanged world footprint. -/
theorem logsLiveOwned_disjoint_store {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {logs : Nat} {x : BitVec 64}
    {mem' : BitVec 64 → HolWordLab 64}
    (hA : ArenaOK s) (hg : GuestInv s) (hgp : GuestInv {s with memory := mem'})
    (hl : LogsListOK s logs) (hd : LogsLiveOwned s S Nd logs)
    (hm : ∀ a, a ≠ x → mem' a = s.memory a)
    (hh : Disj (logs, 24) (x.toNat, 8))
    (ha : Disj (memW s logs, 8 * memW s (logs + 8)) (x.toNat, 8))
    (he : ∀ i, i < memW s (logs + 8) →
      Disj (memW s (memW s logs + 8 * i), 40) (x.toNat, 8))
    (howned : worldOwned {s with memory := mem'} S Nd = worldOwned s S Nd) :
    LogsListOK {s with memory := mem'} logs ∧
      LogsLiveOwned {s with memory := mem'} S Nd logs := by
  let post := {s with memory := mem'}
  by_cases hn : logs = 0
  · exact ⟨Or.inl hn, fun h => False.elim (h hn)⟩
  have hl' := hl.resolve_left hn
  have hu : IvlUnhit s post (logs, 24) := ivlUnhit_single hm (by simp) hh
  have hb := (ivl_allocated_bound hA hl'.2.1).2
  have h0 : memW post logs = memW s logs :=
    memW_eq_of_ivlUnhit hu hl'.1.1 hb ⟨by omega, by omega⟩
  have h8 : memW post (logs + 8) = memW s (logs + 8) :=
    memW_eq_of_ivlUnhit hu (by have := hl'.1.1; omega) hb ⟨by omega, by omega⟩
  have hp : ∀ i, i < memW s (logs + 8) →
      memW post (memW s logs + 8 * i) = memW s (memW s logs + 8 * i) := by
    intro i hi
    have hal := logsListOK_array_aligned hg hl hn (by omega)
    have hua : IvlUnhit s post (memW s logs, 8 * memW s (logs + 8)) :=
      ivlUnhit_single hm (fun _ => hal) ha
    exact memW_eq_of_ivlUnhit hua (by omega)
      (ivl_allocated_bound hA (hd hn).1).2 ⟨by dsimp; omega, by dsimp; omega⟩
  have hue : ∀ i, i < memW s (logs + 8) →
      IvlUnhit s post (memW s (memW s logs + 8 * i), 40) :=
    fun i hi => ivlUnhit_single hm (by simp) (he i hi)
  refine ⟨logsListOK_congr_header_unhit hA hg hgp (by rfl) hl
    (fun h => h) hu hp hue, ?_⟩
  intro _
  change Allocated post (memW post logs, 8 * memW post (logs + 8)) ∧ _
  rw [h0, h8]
  refine ⟨(hd hn).1, ?_, ?_⟩
  · change IvlsDisj _ (worldOwned post S Nd)
    rw [howned]
    exact (hd hn).2.1
  · intro i hi
    rw [hp i hi, logOwnedIvls_eq_of_unhit hA (hl'.2.2.2.2 i hi).2 (hue i hi) rfl]
    change IvlsDisj _ (worldOwned post S Nd)
    rw [howned]
    exact (hd hn).2.2 i hi

/-- The stable length update preserves the source logs and their ownership.
The separation premises are the freshness facts to retain from `lst_new`. -/
theorem stable_length_store_source {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : Phase4StableStorageReady s)
    (hh : Allocated s (locN s "stable_logs", 24))
    (S Nd : List Nat) (hW : WorldTypedWith s S Nd)
    (ho : LogsLiveOwned s S Nd (locN s "logs"))
    (hs : ∀ o ∈ worldOwned s S Nd, Disj (locN s "stable_logs", 24) o)
    (hhead : Disj (locN s "logs", 24) (locN s "stable_logs", 24))
    (harray : Disj (memW s (locN s "logs"), 8 * memW s (locN s "logs" + 8))
      (locN s "stable_logs", 24))
    (hentry : ∀ i, i < memW s (locN s "logs" + 8) →
      Disj (memW s (memW s (locN s "logs") + 8 * i), 40) (locN s "stable_logs", 24))
    (hx : s.memaddrs (BitVec.ofNat 64 (locN s "stable_logs" + 8)))
    (mem' : BitVec 64 → HolWordLab 64)
    (hm : ∀ a, a ≠ BitVec.ofNat 64 (locN s "stable_logs" + 8) → mem' a = s.memory a) :
    let post := {s with memory := mem'}
    WorldTypedWith post S Nd ∧ worldOwned post S Nd = worldOwned s S Nd ∧
      TxEnv post ∧ LogsListOK post (locN s "logs") ∧
      LogsLiveOwned post S Nd (locN s "logs") ∧
      memW post (locN s "logs") = memW s (locN s "logs") ∧
      memW post (locN s "logs" + 8) = memW s (locN s "logs" + 8) := by
  have hptr := hp.1.1.1
  have htw := hptr.1.1.1.1
  have hA := htw.1.1
  have hbound := (stable_length_address_bound s hA.2 hh).1
  have hxin : Inside ((BitVec.ofNat 64 (locN s "stable_logs" + 8)).toNat, 8)
      (locN s "stable_logs") (locN s "stable_logs" + 24) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbound]
    constructor <;> dsimp <;> omega
  obtain ⟨hW', heq, hE'⟩ := store_outside_worldOwned hA htw.2 hW hs hx hxin hm
  have hg : GuestInv {s with memory := mem'} :=
    guestInv_congr (s := s) rfl rfl rfl rfl hA.1
  have hl := hptr.1.1.2.1
  have hr := logsLiveOwned_disjoint_store hA.2 hA.1 hg hl ho hm
    (disj_of_inside_right hxin hhead) (disj_of_inside_right hxin harray)
    (fun i hi => disj_of_inside_right hxin (hentry i hi)) heq
  have hl' := hl.resolve_left hptr.1.2.2
  have hu : IvlUnhit s {s with memory := mem'} (locN s "logs", 24) :=
    ivlUnhit_single hm (by simp) (disj_of_inside_right hxin hhead)
  have hb := (ivl_allocated_bound hA.2 hl'.2.1).2
  exact ⟨hW', heq, hE', hr.1, hr.2,
    memW_eq_of_ivlUnhit hu hl'.1.1 hb ⟨by omega, by omega⟩,
    memW_eq_of_ivlUnhit hu (by have := hl'.1.1; omega) hb ⟨by omega, by omega⟩⟩

/-- The length store needs the separation facts supplied by fresh allocation,
as well as the word shapes of its two local operands. -/
def StableLengthPre : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => Phase4StableStorageReady s ∧
    Allocated s (locN s "stable_logs", 24) ∧
    s.locals.lookup (ofString "stable_logs") =
      some (.val (.word (BitVec.ofNat 64 (locN s "stable_logs")))) ∧
    s.locals.lookup (ofString "nl") = some (.val (.word (BitVec.ofNat 64 (locN s "nl")))) ∧
    ∃ S Nd, WorldTypedWith s S Nd ∧ LogsLiveOwned s S Nd (locN s "logs") ∧
      (∀ o ∈ worldOwned s S Nd, Disj (locN s "stable_logs", 24) o) ∧
      Disj (locN s "logs", 24) (locN s "stable_logs", 24) ∧
      Disj (memW s (locN s "logs"), 8 * memW s (locN s "logs" + 8))
        (locN s "stable_logs", 24) ∧
      ∀ i, i < memW s (locN s "logs" + 8) →
        Disj (memW s (memW s (locN s "logs") + 8 * i), 40) (locN s "stable_logs", 24)

/-- The allocation contract already supplies the capacity inequality for copy setup. -/
theorem stableLengthPre_copy_capacity {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableLengthPre s) (mem' : BitVec 64 → HolWordLab 64) :
    locN {s with memory := mem'} "nl" ≤ locN {s with memory := mem'} "stable_log_cap" := by
  exact (phase4StableCap_bounds s hp.1.1.1).2.1

/-- A memory-only length write retains the three typed setup operands. -/
theorem stableLengthPre_memory_operands {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableLengthPre s) (mem' : BitVec 64 → HolWordLab 64)
    (p : BitVec 64) (hl : s.locals.lookup (ofString "lp") = some (.val (.word p))) :
    ∃ n p w : BitVec 64,
      ({s with memory := mem'} : PanSemStateFiniteExact 64 F).locals.lookup
        (ofString "nl") = some (.val (.word n)) ∧
      ({s with memory := mem'} : PanSemStateFiniteExact 64 F).locals.lookup
        (ofString "lp") = some (.val (.word p)) ∧
      ({s with memory := mem'} : PanSemStateFiniteExact 64 F).locals.lookup
        (ofString "stable_logs") = some (.val (.word w)) := by
  exact ⟨BitVec.ofNat 64 (locN s "nl"), p, BitVec.ofNat 64 (locN s "stable_logs"),
    hp.2.2.2.1, hl, hp.2.2.1⟩

/-- A positive natural local necessarily came from a word-shaped operand. -/
theorem stable_positive_local_word {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name : String) (hp : 0 < locN s name) :
    s.locals.lookup (ofString name) =
      some (.val (.word (BitVec.ofNat 64 (locN s name)))) := by
  unfold locN at hp ⊢
  cases hlookup : s.locals.lookup (ofString name) with
  | none => simp [hlookup] at hp
  | some v =>
    cases v with
    | val value =>
      cases value with
      | word w => simp
    | rStruct _ => simp [hlookup] at hp
    | nStruct _ _ => simp [hlookup] at hp

/-- The allocation return supplies the canonical word representation of the
stable header pointer required by the length store. -/
theorem lst_new_stable_pointer_resume (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    let resumed := setVarHOLFinite (ofString "stable_logs") v {post with locals := s.locals}
    resumed.locals.lookup (ofString "stable_logs") =
      some (.val (.word (BitVec.ofNat 64 (locN resumed "stable_logs")))) := by
  obtain ⟨w, rfl, _⟩ := lst_new_stable_fresh h s vs body callee ret v post hc hp ha hl hr
  simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]

/-- Returning the allocated header preserves the typed length operand. -/
theorem stable_length_operand_resume {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (hn : s.locals.lookup (ofString "nl") =
      some (.val (.word (BitVec.ofNat 64 (locN s "nl"))))) :
    let t := setVarHOLFinite (ofString "stable_logs") v {post with locals := s.locals}
    t.locals.lookup (ofString "nl") =
      some (.val (.word (BitVec.ofNat 64 (locN t "nl")))) := by
  simpa [locN, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
    show ofString "stable_logs" ≠ ofString "nl" by decide] using hn

/-- Package the storage and operand premises needed before the length write. -/
theorem lst_new_stable_length_operands (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (hn : s.locals.lookup (ofString "nl") =
      some (.val (.word (BitVec.ofNat 64 (locN s "nl")))))
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    let t := setVarHOLFinite (ofString "stable_logs") v {post with locals := s.locals}
    Phase4StableStorageReady t ∧ Allocated t (locN t "stable_logs", 24) ∧
      t.locals.lookup (ofString "stable_logs") =
        some (.val (.word (BitVec.ofNat 64 (locN t "stable_logs")))) ∧
      t.locals.lookup (ofString "nl") =
        some (.val (.word (BitVec.ofNat 64 (locN t "nl")))) := by
  exact ⟨lst_new_stable_storage_resume h s vs body callee ret v post hc hp ha hl hr,
    lst_new_stable_header_allocated h s vs body callee ret v post hc hp ha hl hr,
    lst_new_stable_pointer_resume h s vs body callee ret v post hc hp ha hl hr,
    stable_length_operand_resume s post v hn⟩

def StableLengthPost : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => TxWorld s ∧ LogsListOK s (locN s "logs") ∧
    LogsWorldOwned s (locN s "logs") ∧
    locN s "nl" = memW s (locN s "logs" + 8) ∧
    locN s "lp" = memW s (locN s "logs") ∧
    memW s (locN s "stable_logs" + 8) = locN s "nl" ∧
    memW s (locN s "stable_logs" + 8) ≤ memW s (locN s "stable_logs" + 16) ∧
    Allocated s (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
    WordsOK s (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap")

theorem hoare_stable_length_store :
    Hoare StableLengthPre
      (.store (.op .add [.var .local (ofString "stable_logs"), .const 8])
        (.var .local (ofString "nl")))
      (fun r t => r = none → StableLengthPost t) := by
  refine R13Shards.Hoare.store_fall fun s x v mem' hp hx hv hst => ?_
  obtain ⟨hp, hh, hlocal, hnl, S, Nd, hW, ho, hs, hhead, harray, hentry⟩ := hp
  have hA := hp.1.1.1.1.1.1.1.1.1
  have hv' : v = .val (.word (BitVec.ofNat 64 (locN s "nl"))) := by
    change s.locals.lookup (ofString "nl") = some v at hv
    rw [hnl] at hv
    exact (Option.some.inj hv).symm
  subst v
  have hx' : x = BitVec.ofNat 64 (locN s "stable_logs" + 8) := by
    simp [evalAt, evalHOLExact, evalListHOLExact, hlocal, valueIsWord,
      valueWord, wordOpHOL, wordOp] at hx
    subst x
    apply BitVec.eq_of_toNat_eq
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt
      (stable_length_address_bound s hA.2 hh).1] using
      (stable_length_address_bound s hA.2 hh).2
  subst x
  obtain ⟨hdom, he, hm⟩ := R13Shards.panMemStoresHOL_word_spec
    (by simpa only [flattenHOL] using hst)
  obtain ⟨hW', _, hE', hl', ho', h0, h8⟩ :=
    stable_length_store_source s hp hh S Nd hW ho hs hhead harray hentry hdom mem' hm
  have hg : GuestInv {s with memory := mem'} :=
    guestInv_congr (s := s) rfl rfl rfl rfl hA.1
  have hAp : ArenaReady {s with memory := mem'} := ⟨hg, hA.2⟩
  refine ⟨⟨worldOK_of_parts hAp hW', hE'⟩, hl', ⟨S, Nd, hW', ho'⟩,
    ?_, ?_, stable_length_store_value s hp mem' he,
    stable_length_store_fits s hp hA.2 hh mem' he hm,
    stable_length_store_backing s hp hA.2 hh mem' _ he hm⟩
  · exact hp.1.1.1.1.2.1.trans h8.symm
  · exact hp.1.1.1.2.trans h0.symm

theorem stableLengthPost_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat)
    (hl : ∀ name ∈ (["index", "logs", "nl", "lp", "stable_logs", "stable_log_cap"] : List String),
      locals.lookup (ofString name) = s.locals.lookup (ofString name))
    (hp : StableLengthPost s) : StableLengthPost {s with locals := locals, clock := k} := by
  have he : ∀ name ∈ (["index", "logs", "nl", "lp", "stable_logs", "stable_log_cap"] : List String),
      locN {s with locals := locals, clock := k} name = locN s name :=
    fun name hn => locN_congr s locals k name (hl name hn)
  obtain ⟨hW, hlogs, hown, hnl, hlp, hlen, hcap, ha, hw⟩ := hp
  refine ⟨⟨localsFree_worldOK s locals k hW.1,
    txEnv_with_locals s locals k (hl "index" (by simp)) hW.2⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [he "logs" (by simp)]
    exact (R13Shards.logsListOK_with_locals s locals k _).mpr hlogs
  · rw [he "logs" (by simp)]
    exact logsWorldOwned_with_locals locals k hown
  · rw [he "nl" (by simp), he "logs" (by simp)]; exact hnl
  · rw [he "lp" (by simp), he "logs" (by simp)]; exact hlp
  · rw [he "stable_logs" (by simp), he "nl" (by simp)]; exact hlen
  · rw [he "stable_logs" (by simp)]; exact hcap
  · rw [he "stable_logs" (by simp), he "stable_log_cap" (by simp)]; exact ha
  · rw [he "stable_logs" (by simp), he "stable_log_cap" (by simp)]; exact hw

theorem localsOnly_stableLengthPost :
    LocalsOnly ["index", "logs", "nl", "lp", "stable_logs", "stable_log_cap"] StableLengthPost := by
  intro F s locals k hl hp
  exact stableLengthPost_with_locals s locals k hl hp

/-- Initializing the stable backing operand preserves the length postcondition. -/
theorem stableLengthPost_set_backing {F : Type} (s : PanSemStateFiniteExact 64 F)
    (v : ValueHOL 64) (hp : StableLengthPost s) :
    StableLengthPost (setVarHOLFinite (ofString "stable_lp") v s) := by
  apply stableLengthPost_with_locals s _ s.clock _ hp
  intro name hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [HolFiniteMapExact.lookup_update, FUPDATE, ofString]

/-- Reassemble the length postcondition after a copy write. The destination
header and source header are framed, and word validity is transported by the
guest memory-domain invariant. -/
theorem stableLengthPost_copy_store {F : Type} (s : PanSemStateFiniteExact 64 F)
    (mem' : BitVec 64 → HolWordLab 64) (hp : StableLengthPost s)
    (hworld : TxWorld {s with memory := mem'})
    (hlogs : LogsListOK {s with memory := mem'} (locN s "logs"))
    (hown : LogsWorldOwned {s with memory := mem'} (locN s "logs"))
    (hsrc0 : memW {s with memory := mem'} (locN s "logs") = memW s (locN s "logs"))
    (hsrc8 : memW {s with memory := mem'} (locN s "logs" + 8) = memW s (locN s "logs" + 8))
    (hdst0 : memW {s with memory := mem'} (locN s "stable_logs") = memW s (locN s "stable_logs"))
    (hdst8 : memW {s with memory := mem'} (locN s "stable_logs" + 8) =
      memW s (locN s "stable_logs" + 8))
    (hdst16 : memW {s with memory := mem'} (locN s "stable_logs" + 16) =
      memW s (locN s "stable_logs" + 16)) :
    StableLengthPost {s with memory := mem'} := by
  obtain ⟨hW, _, _, hnl, hlp, hlen, hcap, ha, hw⟩ := hp
  refine ⟨hworld, hlogs, hown, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hnl.trans hsrc8.symm
  · exact hlp.trans hsrc0.symm
  · change memW {s with memory := mem'} (locN s "stable_logs" + 8) = locN s "nl"
    rw [hdst8]; exact hlen
  · change memW {s with memory := mem'} (locN s "stable_logs" + 8) ≤
      memW {s with memory := mem'} (locN s "stable_logs" + 16)
    rw [hdst8, hdst16]; exact hcap
  · change Allocated {s with memory := mem'}
      (memW {s with memory := mem'} (locN s "stable_logs"), 8 * locN s "stable_log_cap")
    rw [hdst0]; exact ha
  · change WordsOK {s with memory := mem'}
      (memW {s with memory := mem'} (locN s "stable_logs"), 8 * locN s "stable_log_cap")
    rw [hdst0]
    exact wordsOK_transfer hW.1.1.1 hworld.1.1.1 hw

/-- Connect the actual length write at spine position 133 to its continuation. -/
theorem phase4StableLength_cut {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn StableLengthPost tail b) :
    TerminatingProgBoundedOn StableLengthPre
      (spinePlug 1 (spineAt 133 ptxCode) tail) b := by
  have hb := @seq_bound_trans _ _ _ _ _ _
    (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
    hoare_stable_length_store htail
  unfold ptxCode
  intro F s hc hp
  have hr := hb s hc hp
  simp only [Nat.zero_add] at hr
  exact hr

/-- The copied length inherits the source list's receipt-size bound. -/
theorem stableLengthPost_length_bound {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableLengthPost s) (hn : locN s "logs" ≠ 0) :
    locN s "nl" < 2 ^ 28 ∧ memW s (locN s "stable_logs" + 8) < 2 ^ 28 := by
  have hl := hp.2.1.resolve_left hn
  have hb : locN s "nl" < 2 ^ 28 := by
    rw [hp.2.2.2.1]
    exact hl.2.2.1
  exact ⟨hb, hp.2.2.2.2.2.1.symm ▸ hb⟩

/-- At loop exit, equality of the live pointer cells transfers log-entry
validity from the source list to the stable list. -/
theorem stable_copy_complete {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableLengthPost s) (hn : locN s "logs" ≠ 0)
    (hh : WordsOK s (locN s "stable_logs", 24))
    (ha : Allocated s (locN s "stable_logs", 24))
    (hcap : locN s "nl" ≤ locN s "stable_log_cap")
    (hcopy : ∀ i, i < locN s "nl" →
      memW s (memW s (locN s "stable_logs") + 8 * i) =
        memW s (memW s (locN s "logs") + 8 * i)) :
    PtxReceiptsDone s := by
  have hl := hp.2.1.resolve_left hn
  have hb := stableLengthPost_length_bound s hp hn
  have hlen := hp.2.2.2.2.2.1
  have hfits := hp.2.2.2.2.2.2.1
  have hwords := hp.2.2.2.2.2.2.2.2
  refine ⟨hp.1, Or.inr ⟨hh, ha, hb.2, hfits, ?_⟩, hb.2⟩
  intro i hi
  rw [hlen] at hi
  refine ⟨?_, ?_⟩
  · apply hwords.2.2 i
    have hic : i < locN s "stable_log_cap" := lt_of_lt_of_le hi hcap
    simpa using hic
  · rw [hcopy i hi]
    exact (hl.2.2.2.2 i (by rw [← hp.2.2.2.1]; exact hi)).2

/-- The stable-copy loop records equality only for the already copied prefix. -/
def StableCopyInv : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => StableLengthPost s ∧ locN s "logs" ≠ 0 ∧
    WordsOK s (locN s "stable_logs", 24) ∧
    Allocated s (locN s "stable_logs", 24) ∧
    locN s "nl" ≤ locN s "stable_log_cap" ∧
    ∀ i, i < locN s "i" → i < locN s "nl" →
      memW s (memW s (locN s "stable_logs") + 8 * i) =
        memW s (memW s (locN s "logs") + 8 * i)

/-- The allocated stable header supplies the non-null word used by the receipt push. -/
theorem stableCopyInv_stable_local {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableCopyInv s) :
    locN s "stable_logs" ≠ 0 ∧
      ∃ w : BitVec 64, s.locals.lookup (ofString "stable_logs") = some (.val (.word w)) := by
  have hA : ArenaOK s := hp.1.1.1.1.2
  have hn : locN s "stable_logs" ≠ 0 := by
    have hb : 0 < sourceBase := by decide
    have hs : 0 < scratchStart := by decide
    rcases hp.2.2.2.1 with hh | hh
    · have := hh.1; omega
    · have := hh.1
      have := hA.2.2.1
      have := hA.2.2.2.1
      omega
  refine ⟨hn, ?_⟩
  cases hl : s.locals.lookup (ofString "stable_logs") with
  | none => simp [locN, hl] at hn
  | some v =>
    cases v with
    | val x =>
      cases x with
      | word w => exact ⟨w, rfl⟩
    | _ => simp [locN, hl] at hn

/-- The loop invariant survives clock changes and unrelated temporary locals. -/
theorem stableCopyInv_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat)
    (hl : ∀ name ∈ (["index", "logs", "nl", "lp", "stable_logs", "stable_log_cap", "i"] : List String),
      locals.lookup (ofString name) = s.locals.lookup (ofString name))
    (hp : StableCopyInv s) : StableCopyInv {s with locals := locals, clock := k} := by
  have he : ∀ name ∈ (["logs", "nl", "stable_logs", "stable_log_cap", "i"] : List String),
      locN {s with locals := locals, clock := k} name = locN s name := by
    intro name hn
    apply locN_congr s locals k name
    apply hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn ⊢
    tauto
  refine ⟨stableLengthPost_with_locals s locals k (fun name hn => hl name (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn ⊢; tauto)) hp.1, ?_, ?_, ?_, ?_, ?_⟩
  · rw [he "logs" (by simp)]; exact hp.2.1
  · rw [he "stable_logs" (by simp)]; exact hp.2.2.1
  · rw [he "stable_logs" (by simp)]; exact hp.2.2.2.1
  · rw [he "nl" (by simp), he "stable_log_cap" (by simp)]; exact hp.2.2.2.2.1
  · intro j hj hn
    rw [he "i" (by simp)] at hj
    rw [he "nl" (by simp)] at hn
    rw [he "stable_logs" (by simp), he "logs" (by simp)]
    exact hp.2.2.2.2.2 j hj hn

/-- Clock consumption at a while boundary preserves the copy invariant. -/
theorem stableCopyInv_decClock {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableCopyInv s) : StableCopyInv (decClockHOLFinite s) := by
  exact stableCopyInv_with_locals s s.locals (s.clock - 1) (fun _ _ => rfl) hp

theorem stableCopyInv_zero {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableLengthPost s) (hn : locN s "logs" ≠ 0)
    (hh : WordsOK s (locN s "stable_logs", 24))
    (ha : Allocated s (locN s "stable_logs", 24))
    (hcap : locN s "nl" ≤ locN s "stable_log_cap")
    (hj : locN s "i" = 0) : StableCopyInv s := by
  refine ⟨hp, hn, hh, ha, hcap, ?_⟩
  intro i hi _
  omega

/-- The actual zero counter initialization establishes the copy invariant. -/
theorem stableCopyInv_init {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableLengthPost s) (hn : locN s "logs" ≠ 0)
    (hh : WordsOK s (locN s "stable_logs", 24))
    (ha : Allocated s (locN s "stable_logs", 24))
    (hcap : locN s "nl" ≤ locN s "stable_log_cap") :
    StableCopyInv (setVarHOLFinite (ofString "i") (.val (.word 0)) s) := by
  have hpost : StableLengthPost (setVarHOLFinite (ofString "i") (.val (.word 0)) s) :=
    LocalsOnly.setVar localsOnly_stableLengthPost (by decide) _ s hp
  apply stableCopyInv_zero _ hpost
  · simpa [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "i" ≠ ofString "logs" from by decide] using hn
  · change WordsOK s _
    simpa [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "i" ≠ ofString "stable_logs" from by decide] using hh
  · change Allocated s _
    simpa [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "i" ≠ ofString "stable_logs" from by decide] using ha
  · simpa [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "i" ≠ ofString "nl" from by decide,
      show ofString "i" ≠ ofString "stable_log_cap" from by decide] using hcap
  · simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]

/-- Hoare rule for the counter initialization before the stable-copy loop. -/
theorem hoare_stableCopy_init :
    Hoare (fun s => StableLengthPost s ∧ locN s "logs" ≠ 0 ∧
      WordsOK s (locN s "stable_logs", 24) ∧ Allocated s (locN s "stable_logs", 24) ∧
      locN s "nl" ≤ locN s "stable_log_cap")
      (.assign .local (ofString "i") (.const 0))
      (fun r t => r = none → StableCopyInv t) := by
  apply Hoare.assign
  · intro F s v hp hv _
    have hv' : v = .val (.word 0) := by
      simpa [evalAt, evalHOLExact] using hv.symm
    subst v
    exact stableCopyInv_init s hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2
  · intro F s hp hr
    exact absurd hr (by simp)

theorem stableCopyInv_source_word {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableCopyInv s) (hj : locN s "i" < locN s "nl") :
    WordAt s (locN s "lp" + 8 * locN s "i") ∧
      LogEntryOK s (memW s (locN s "lp" + 8 * locN s "i")) := by
  have hl := hp.1.2.1.resolve_left hp.2.1
  rw [hp.1.2.2.2.2.1]
  exact hl.2.2.2.2 (locN s "i") (by rw [← hp.1.2.2.2.1]; exact hj)

theorem stableCopyInv_destination_word {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableCopyInv s) (hi : locN s "i" < locN s "nl") :
    WordAt s (memW s (locN s "stable_logs") + 8 * locN s "i") := by
  have hw := hp.1.2.2.2.2.2.2.2.2
  have hcap := hp.2.2.2.2.1
  apply hw.2.2 (locN s "i")
  have hic : locN s "i" < locN s "stable_log_cap" := lt_of_lt_of_le hi hcap
  simpa using hic

theorem stableCopyInv_destination_bound {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableCopyInv s) (hi : locN s "i" < locN s "nl") :
    memW s (locN s "stable_logs") + 8 * locN s "nl" ≤ 2 ^ 64 ∧
      memW s (locN s "stable_logs") + 8 * locN s "i" < 2 ^ 64 := by
  have ha := hp.1.2.2.2.2.2.2.2.1
  have hA := hp.1.1.1.1.2
  have hb := (ivl_allocated_bound hA ha).2
  have hc := hp.2.2.2.2.1
  dsimp at hb
  constructor <;> omega

theorem stableCopyInv_source_bound {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableCopyInv s) (hi : locN s "i" < locN s "nl") :
    locN s "lp" + 8 * locN s "nl" ≤ 2 ^ 64 ∧
      locN s "lp" + 8 * locN s "i" < 2 ^ 64 := by
  obtain ⟨S, Nd, _, ho⟩ := hp.1.2.2.1
  have hb := (ivl_allocated_bound hp.1.1.1.1.2 (ho hp.2.1).1).2
  rw [hp.1.2.2.2.2.1, hp.1.2.2.2.1] at *
  dsimp at hb
  constructor <;> omega

theorem stableCopyInv_source_aligned {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableCopyInv s) (hi : locN s "i" < locN s "nl") :
    locN s "lp" % 8 = 0 := by
  rw [hp.1.2.2.2.2.1]
  apply logsListOK_array_aligned hp.1.1.1.1.1 hp.1.2.1 hp.2.1
  rw [← hp.1.2.2.2.1]
  omega

theorem stableCopyInv_offset_word {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableCopyInv s) (hi : locN s "i" < locN s "nl") :
    (BitVec.ofNat 64 (locN s "i") * (8 : BitVec 64)).toNat = 8 * locN s "i" := by
  have hb := (stableCopyInv_source_bound s hp hi).2
  have hi' : locN s "i" < 2 ^ 64 := by omega
  have hm : locN s "i" * 8 < 2 ^ 64 := by omega
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi']
  change locN s "i" * 8 % 2 ^ 64 = 8 * locN s "i"
  rw [Nat.mod_eq_of_lt hm, Nat.mul_comm]

theorem stableCopyInv_address_words {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableCopyInv s) (hi : locN s "i" < locN s "nl") :
    (BitVec.ofNat 64 (locN s "lp") +
      BitVec.ofNat 64 (8 * locN s "i")).toNat = locN s "lp" + 8 * locN s "i" ∧
    (BitVec.ofNat 64 (memW s (locN s "stable_logs")) +
      BitVec.ofNat 64 (8 * locN s "i")).toNat =
        memW s (locN s "stable_logs") + 8 * locN s "i" := by
  have hs := (stableCopyInv_source_bound s hp hi).2
  have hd := (stableCopyInv_destination_bound s hp hi).2
  have hi' : 8 * locN s "i" < 2 ^ 64 := by omega
  have hs' : locN s "lp" < 2 ^ 64 := by omega
  have hd' : memW s (locN s "stable_logs") < 2 ^ 64 := by omega
  constructor <;> simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hi', Nat.mod_eq_of_lt hs', Nat.mod_eq_of_lt hd',
    Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hd]

/-- The natural remaining-copy rank has a uniform bound from the source length. -/
theorem stableCopyInv_rank_bound {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableCopyInv s) : locN s "nl" - locN s "i" < 2 ^ 28 := by
  have hn := (stableLengthPost_length_bound s hp.1 hp.2.1).1
  omega

/-- Interpret the signed loop comparison in the bounded natural index range. -/
theorem stableCopyInv_guard {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableCopyInv s) (i n w : BitVec 64)
    (hi : s.locals.lookup (ofString "i") = some (.val (.word i)))
    (hn : s.locals.lookup (ofString "nl") = some (.val (.word n)))
    (hib : locN s "i" < 2 ^ 63)
    (he : evalAt s (.cmp .less (.var .local (ofString "i"))
      (.var .local (ofString "nl"))) = some (.val (.word w)))
    (hw : w ≠ 0) : locN s "i" < locN s "nl" := by
  have hnb := (stableLengthPost_length_bound s hp.1 hp.2.1).1
  have hil : locN s "i" = i.toNat := by simp [locN, hi]
  have hnl : locN s "nl" = n.toNat := by simp [locN, hn]
  rw [hil] at hib ⊢
  rw [hnl] at hnb ⊢
  have hnb' : n.toNat < 2 ^ 63 := by omega
  have hc : Compiler.Encoders.Asm.wordCmpHOL .less i n = true := by
    by_contra hc
    simp [evalAt, evalHOLExact, hi, hn, hc] at he
    exact hw he.symm
  norm_num at hib hnb'
  simpa [Compiler.Encoders.Asm.wordCmpHOL, Compiler.Encoders.Asm.holAsmSignedLess,
    hib, hnb'] using hc

/-- A false signed guard certifies completion of the bounded copy prefix. -/
theorem stableCopyInv_guard_false {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableCopyInv s) (i n : BitVec 64)
    (hi : s.locals.lookup (ofString "i") = some (.val (.word i)))
    (hn : s.locals.lookup (ofString "nl") = some (.val (.word n)))
    (hib : locN s "i" < 2 ^ 63)
    (he : evalAt s (.cmp .less (.var .local (ofString "i"))
      (.var .local (ofString "nl"))) = some (.val (.word 0))) :
    locN s "nl" ≤ locN s "i" := by
  have hnb := (stableLengthPost_length_bound s hp.1 hp.2.1).1
  have hil : locN s "i" = i.toNat := by simp [locN, hi]
  have hnl : locN s "nl" = n.toNat := by simp [locN, hn]
  rw [hil] at hib ⊢
  rw [hnl] at hnb ⊢
  have hnb' : n.toNat < 2 ^ 63 := by omega
  norm_num at hib hnb'
  have hnot : ¬ i.toNat < n.toNat := by
    simpa [evalAt, evalHOLExact, hi, hn, Compiler.Encoders.Asm.wordCmpHOL,
      Compiler.Encoders.Asm.holAsmSignedLess, hib, hnb'] using he
  omega

theorem stableCopyInv_exit {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableCopyInv s) (hexit : locN s "nl" ≤ locN s "i") :
    PtxReceiptsDone s := by
  obtain ⟨hp, hn, hh, ha, hcap, hcopy⟩ := hp
  exact stable_copy_complete s hp hn hh ha hcap
    (fun i hi => hcopy i (lt_of_lt_of_le hi hexit) hi)

/-- The copied live prefix fits inside the allocated stable backing capacity. -/
theorem stableCopyInv_live_allocated {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableCopyInv s) :
    Allocated s (memW s (locN s "stable_logs"),
      8 * memW s (locN s "stable_logs" + 8)) := by
  have ha := hp.1.2.2.2.2.2.2.2.1
  have hn := hp.1.2.2.2.2.2.1
  have hc := hp.2.2.2.2.1
  rw [hn]
  rcases ha with ha | ha
  · exact Or.inl ⟨ha.1, by have := ha.2; dsimp at *; omega⟩
  · exact Or.inr ⟨ha.1, by have := ha.2; dsimp at *; omega⟩

/-- At copy completion, source record ownership transfers to the stable list
when its header and live backing remain separated from the same world. -/
theorem stableCopyInv_exit_owned {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableCopyInv s) (hexit : locN s "nl" ≤ locN s "i")
    {S Nd : List Nat} (hown : LogsLiveOwned s S Nd (locN s "logs"))
    (hsep : IvlsDisj [(locN s "stable_logs", 24),
      (memW s (locN s "stable_logs"), 8 * memW s (locN s "stable_logs" + 8))]
      (worldOwned s S Nd)) :
    LogsLiveOwned s S Nd (locN s "stable_logs") := by
  intro _
  refine ⟨stableCopyInv_live_allocated s hp, hsep, ?_⟩
  intro j hj
  have hlen := hp.1.2.2.2.2.2.1
  have hsource := hp.1.2.2.2.1
  have hjn : j < locN s "nl" := by simpa only [hlen] using hj
  rw [hp.2.2.2.2.2 j (lt_of_lt_of_le hjn hexit) hjn]
  exact (hown hp.2.1).2.2 j (by simpa only [← hsource] using hjn)

/-- Header separation and capacity separation suffice for live-list ownership
at exit; all copied records inherit the source's world separation. -/
theorem stableCopyInv_exit_owned_of_capacity {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hp : StableCopyInv s)
    (hexit : locN s "nl" ≤ locN s "i") {S Nd : List Nat}
    (hown : LogsLiveOwned s S Nd (locN s "logs"))
    (hhead : ∀ o ∈ worldOwned s S Nd, Disj (locN s "stable_logs", 24) o)
    (hback : ∀ o ∈ worldOwned s S Nd,
      Disj (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") o) :
    LogsLiveOwned s S Nd (locN s "stable_logs") := by
  apply stableCopyInv_exit_owned s hp hexit hown
  intro a ha o ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact hhead o ho
  · apply disj_of_inside_left ?_ (hback o ho)
    have hn := hp.1.2.2.2.2.2.1
    have hc := hp.2.2.2.2.1
    constructor <;> dsimp <;> omega

/-- Exhaustion of the natural copy rank yields the receipt postcondition. -/
theorem stableCopyInv_rank_zero_exit {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableCopyInv s) (hz : locN s "nl" - locN s "i" = 0) :
    PtxReceiptsDone s := by
  apply stableCopyInv_exit s hp
  omega

/-- Separation from the whole backing allocation implies separation from
the current copy destination, including its machine-address conversion. -/
theorem stableCopyInv_destination_disj {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableCopyInv s) (hi : locN s "i" < locN s "nl")
    {region : Ivl}
    (hd : Disj region (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap")) :
    Disj region
      ((BitVec.ofNat 64 (memW s (locN s "stable_logs") + 8 * locN s "i")).toNat, 8) := by
  apply disj_of_inside_right ?_ hd
  rw [BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (stableCopyInv_destination_bound s hp hi).2]
  have hc := hp.2.2.2.2.1
  constructor <;> dsimp <;> omega

/-- A copy write preserves any allocated header separated from the backing
array. This supplies the source and destination header frame obligations. -/
theorem stableCopyInv_header_unhit {F : Type} (s : PanSemStateFiniteExact 64 F)
    (mem' : BitVec 64 → HolWordLab 64) (hp : StableCopyInv s)
    (hi : locN s "i" < locN s "nl") (p : Nat)
    (ha : Allocated s (p, 24)) (hal : p % 8 = 0)
    (hd : Disj (p, 24) (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap"))
    (hm : ∀ a, a ≠ BitVec.ofNat 64
      (memW s (locN s "stable_logs") + 8 * locN s "i") → mem' a = s.memory a) :
    memW {s with memory := mem'} p = memW s p ∧
      memW {s with memory := mem'} (p + 8) = memW s (p + 8) ∧
      memW {s with memory := mem'} (p + 16) = memW s (p + 16) := by
  have hu : IvlUnhit s {s with memory := mem'} (p, 24) :=
    ivlUnhit_single hm (by simp) (stableCopyInv_destination_disj s hp hi hd)
  have hb := (ivl_allocated_bound hp.1.1.1.1.2 ha).2
  refine ⟨memW_eq_of_ivlUnhit hu hal hb ⟨by omega, by omega⟩, ?_, ?_⟩
  · exact memW_eq_of_ivlUnhit hu (by omega) hb ⟨by omega, by omega⟩
  · exact memW_eq_of_ivlUnhit hu (by omega) hb ⟨by omega, by omega⟩

/-- The semantic memory step of the stable-copy loop extends the copied
prefix by one cell. The source is framed, and destination addresses do not wrap. -/
theorem stable_copy_prefix_step {F : Type} (s : PanSemStateFiniteExact 64 F)
    (mem' : BitVec 64 → HolWordLab 64) (dst src i n : Nat)
    (hi : i < n) (hbound : dst + 8 * n ≤ 2 ^ 64)
    (hprefix : ∀ j, j < i → memW s (dst + 8 * j) = memW s (src + 8 * j))
    (hwrite : memW {s with memory := mem'} (dst + 8 * i) = memW s (src + 8 * i))
    (hm : ∀ a, a ≠ BitVec.ofNat 64 (dst + 8 * i) → mem' a = s.memory a)
    (hsource : ∀ j, j < n →
      memW {s with memory := mem'} (src + 8 * j) = memW s (src + 8 * j)) :
    ∀ j, j < i + 1 →
      memW {s with memory := mem'} (dst + 8 * j) =
        memW {s with memory := mem'} (src + 8 * j) := by
  intro j hj
  rw [hsource j (by omega)]
  by_cases he : j = i
  · subst j; exact hwrite
  have hji : j < i := by omega
  have hdi : dst + 8 * i < 2 ^ 64 := by omega
  have hdj : dst + 8 * j < 2 ^ 64 := by omega
  have hne : BitVec.ofNat 64 (dst + 8 * j) ≠ BitVec.ofNat 64 (dst + 8 * i) := by
    intro heq
    have heq' := congrArg BitVec.toNat heq
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdi, Nat.mod_eq_of_lt hdj] at heq'
    omega
  calc
    memW {s with memory := mem'} (dst + 8 * j) = memW s (dst + 8 * j) := by
      simp only [memW]
      rw [hm _ hne]
    _ = memW s (src + 8 * j) := hprefix j hji

/-- Instantiate prefix extension with the addresses and bound carried by
the stable-copy invariant. -/
theorem stableCopyInv_store_prefix {F : Type} (s : PanSemStateFiniteExact 64 F)
    (mem' : BitVec 64 → HolWordLab 64) (hp : StableCopyInv s)
    (hi : locN s "i" < locN s "nl")
    (hwrite : memW {s with memory := mem'}
      (memW s (locN s "stable_logs") + 8 * locN s "i") =
      memW s (memW s (locN s "logs") + 8 * locN s "i"))
    (hm : ∀ a, a ≠ BitVec.ofNat 64
      (memW s (locN s "stable_logs") + 8 * locN s "i") → mem' a = s.memory a)
    (hsource : ∀ j, j < locN s "nl" →
      memW {s with memory := mem'} (memW s (locN s "logs") + 8 * j) =
        memW s (memW s (locN s "logs") + 8 * j))
    (hsrc : memW {s with memory := mem'} (locN s "logs") = memW s (locN s "logs"))
    (hdst : memW {s with memory := mem'} (locN s "stable_logs") =
      memW s (locN s "stable_logs")) :
    ∀ j, j < locN s "i" + 1 →
      memW {s with memory := mem'}
          (memW {s with memory := mem'} (locN s "stable_logs") + 8 * j) =
        memW {s with memory := mem'}
          (memW {s with memory := mem'} (locN s "logs") + 8 * j) := by
  intro j hj
  rw [hsrc, hdst]
  exact stable_copy_prefix_step s mem' _ _ _ _ hi
    (stableCopyInv_destination_bound s hp hi).1
    (fun k hk => hp.2.2.2.2.2 k hk (lt_trans hk hi)) hwrite hm hsource j hj

/-- A destination write outside the source array preserves every source
pointer cell, providing the frame premise of `stable_copy_prefix_step`. -/
theorem stable_copy_source_cells {F : Type} (s : PanSemStateFiniteExact 64 F)
    (mem' : BitVec 64 → HolWordLab 64) (src n : Nat) (x : BitVec 64)
    (hA : ArenaOK s) (ha : Allocated s (src, 8 * n)) (hal : src % 8 = 0)
    (hd : Disj (src, 8 * n) (x.toNat, 8))
    (hm : ∀ a, a ≠ x → mem' a = s.memory a) :
    ∀ j, j < n → memW {s with memory := mem'} (src + 8 * j) = memW s (src + 8 * j) := by
  have hu : IvlUnhit s {s with memory := mem'} (src, 8 * n) :=
    ivlUnhit_single hm (fun _ => hal) hd
  intro j hj
  exact memW_eq_of_ivlUnhit hu (by omega) (ivl_allocated_bound hA ha).2
    ⟨by dsimp; omega, by dsimp; omega⟩

/-- The stable length write preserves each source pointer cell, enabling
record separation to be transported into the copy-loop entry state. -/
theorem stable_length_source_cells {F : Type} (s : PanSemStateFiniteExact 64 F)
    (mem' : BitVec 64 → HolWordLab 64) (src n : Nat)
    (hA : ArenaOK s) (hh : Allocated s (locN s "stable_logs", 24))
    (ha : Allocated s (src, 8 * n)) (hal : src % 8 = 0)
    (hd : Disj (src, 8 * n) (locN s "stable_logs", 24))
    (hm : ∀ a, a ≠ BitVec.ofNat 64 (locN s "stable_logs" + 8) →
      mem' a = s.memory a) :
    ∀ j, j < n → memW {s with memory := mem'} (src + 8 * j) =
      memW s (src + 8 * j) := by
  apply stable_copy_source_cells s mem' src n _ hA ha hal _ hm
  apply disj_of_inside_right _ hd
  rw [BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (stable_length_address_bound s hA hh).1]
  constructor <;> dsimp <;> omega

/-- The length-store precondition discharges source-array framing without
requiring a separate allocation or alignment hypothesis. -/
theorem stableLengthPre_source_cells {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableLengthPre s) (mem' : BitVec 64 → HolWordLab 64)
    (hm : ∀ a, a ≠ BitVec.ofNat 64 (locN s "stable_logs" + 8) → mem' a = s.memory a) :
    ∀ j, j < memW s (locN s "logs" + 8) →
      memW {s with memory := mem'} (memW s (locN s "logs") + 8 * j) =
        memW s (memW s (locN s "logs") + 8 * j) := by
  obtain ⟨S, Nd, hW, ho, hs, hh, ha, he⟩ := hp.2.2.2.2
  have hptr := hp.1.1.1.1
  have htw := hptr.1.1.1.1
  intro j hj
  exact stable_length_source_cells s mem' _ _ htw.1.1.2 hp.2.1
    (ho hptr.1.2.2).1
    (logsListOK_array_aligned htw.1.1.1 hptr.1.1.2.1 hptr.1.2.2 (by omega))
    ha hm j hj

/-- Specialize source-array framing to the current stable-copy write. -/
theorem stableCopyInv_source_preserved {F : Type} (s : PanSemStateFiniteExact 64 F)
    (mem' : BitVec 64 → HolWordLab 64) (hp : StableCopyInv s)
    (hi : locN s "i" < locN s "nl")
    (hd : Disj (locN s "lp", 8 * locN s "nl")
      (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap"))
    (hm : ∀ a, a ≠ BitVec.ofNat 64
      (memW s (locN s "stable_logs") + 8 * locN s "i") → mem' a = s.memory a) :
    ∀ j, j < locN s "nl" →
      memW {s with memory := mem'} (locN s "lp" + 8 * j) =
        memW s (locN s "lp" + 8 * j) := by
  obtain ⟨S, Nd, _, ho⟩ := hp.1.2.2.1
  have ha : Allocated s (locN s "lp", 8 * locN s "nl") := by
    rw [hp.1.2.2.2.2.1, hp.1.2.2.2.1]
    exact (ho hp.2.1).1
  exact stable_copy_source_cells s mem' _ _ _ hp.1.1.1.1.2 ha
    (stableCopyInv_source_aligned s hp hi)
    (stableCopyInv_destination_disj s hp hi hd) hm

/-- A copy destination outside the world footprint preserves world typing,
the footprint itself, and the transaction environment. -/
theorem stableCopyInv_world_preserved {F : Type} (s : PanSemStateFiniteExact 64 F)
    (mem' : BitVec 64 → HolWordLab 64) (hp : StableCopyInv s)
    (hi : locN s "i" < locN s "nl") (S Nd : List Nat)
    (hW : WorldTypedWith s S Nd)
    (hd : ∀ o ∈ worldOwned s S Nd,
      Disj (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") o)
    (hx : s.memaddrs (BitVec.ofNat 64
      (memW s (locN s "stable_logs") + 8 * locN s "i")))
    (hm : ∀ a, a ≠ BitVec.ofNat 64
      (memW s (locN s "stable_logs") + 8 * locN s "i") → mem' a = s.memory a) :
    WorldTypedWith {s with memory := mem'} S Nd ∧
      worldOwned {s with memory := mem'} S Nd = worldOwned s S Nd ∧
      TxEnv {s with memory := mem'} := by
  apply store_outside_worldOwned hp.1.1.1.1 hp.1.1.2 hW hd hx ?_ hm
  rw [BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (stableCopyInv_destination_bound s hp hi).2]
  have hc := hp.2.2.2.2.1
  constructor <;> dsimp <;> omega

/-- Preserve source validity and live ownership across the current copy
write using separation from the complete stable backing allocation. -/
theorem stableCopyInv_logs_preserved {F : Type} (s : PanSemStateFiniteExact 64 F)
    (mem' : BitVec 64 → HolWordLab 64) (hp : StableCopyInv s)
    (hi : locN s "i" < locN s "nl") (S Nd : List Nat)
    (ho : LogsLiveOwned s S Nd (locN s "logs"))
    (hg : GuestInv {s with memory := mem'})
    (hworld : worldOwned {s with memory := mem'} S Nd = worldOwned s S Nd)
    (hh : Disj (locN s "logs", 24)
      (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap"))
    (ha : Disj (memW s (locN s "logs"), 8 * memW s (locN s "logs" + 8))
      (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap"))
    (he : ∀ j, j < memW s (locN s "logs" + 8) →
      Disj (memW s (memW s (locN s "logs") + 8 * j), 40)
        (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap"))
    (hm : ∀ a, a ≠ BitVec.ofNat 64
      (memW s (locN s "stable_logs") + 8 * locN s "i") → mem' a = s.memory a) :
    LogsListOK {s with memory := mem'} (locN s "logs") ∧
      LogsLiveOwned {s with memory := mem'} S Nd (locN s "logs") := by
  exact logsLiveOwned_disjoint_store hp.1.1.1.1.2 hp.1.1.1.1.1 hg hp.1.2.1 ho hm
    (stableCopyInv_destination_disj s hp hi hh)
    (stableCopyInv_destination_disj s hp hi ha)
    (fun j hj => stableCopyInv_destination_disj s hp hi (he j hj)) hworld

/-- Assemble world, source ownership, and header fields of the length
postcondition after a separated copy write. -/
theorem stableCopyInv_store_post {F : Type} (s : PanSemStateFiniteExact 64 F)
    (mem' : BitVec 64 → HolWordLab 64) (hp : StableCopyInv s)
    (hi : locN s "i" < locN s "nl") (S Nd : List Nat)
    (hW : WorldTypedWith s S Nd) (ho : LogsLiveOwned s S Nd (locN s "logs"))
    (hworld : ∀ o ∈ worldOwned s S Nd,
      Disj (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") o)
    (hh : Disj (locN s "logs", 24)
      (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap"))
    (hd : Disj (locN s "stable_logs", 24)
      (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap"))
    (ha : Disj (memW s (locN s "logs"), 8 * memW s (locN s "logs" + 8))
      (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap"))
    (he : ∀ j, j < memW s (locN s "logs" + 8) →
      Disj (memW s (memW s (locN s "logs") + 8 * j), 40)
        (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap"))
    (hx : s.memaddrs (BitVec.ofNat 64
      (memW s (locN s "stable_logs") + 8 * locN s "i")))
    (hm : ∀ a, a ≠ BitVec.ofNat 64
      (memW s (locN s "stable_logs") + 8 * locN s "i") → mem' a = s.memory a) :
    StableLengthPost {s with memory := mem'} := by
  obtain ⟨hW', hw', hE'⟩ := stableCopyInv_world_preserved s mem' hp hi S Nd hW hworld hx hm
  have hg : GuestInv {s with memory := mem'} :=
    guestInv_congr (s := s) rfl rfl rfl rfl hp.1.1.1.1.1
  obtain ⟨hl', ho'⟩ := stableCopyInv_logs_preserved s mem' hp hi S Nd ho hg hw' hh ha he hm
  have hl := hp.1.2.1.resolve_left hp.2.1
  obtain ⟨hs0, hs8, _⟩ := stableCopyInv_header_unhit s mem' hp hi _ hl.2.1 hl.1.1 hh hm
  obtain ⟨hd0, hd8, hd16⟩ := stableCopyInv_header_unhit s mem' hp hi _
    hp.2.2.2.1 hp.2.2.1.1 hd hm
  exact stableLengthPost_copy_store s mem' hp.1
    ⟨worldOK_of_parts ⟨hg, hp.1.1.1.1.2⟩ hW', hE'⟩ hl' ⟨S, Nd, hW', ho'⟩
    hs0 hs8 hd0 hd8 hd16

/-- Multiplication in the copy offset evaluates to the corresponding word. -/
theorem stable_copy_mul_eval {F : Type} (s : PanSemStateFiniteExact 64 F)
    (w : BitVec 64)
    (hw : s.locals.lookup (ofString "i") = some (.val (.word w))) :
    evalAt s (.panop .mul [.var .local (ofString "i"), .const 8]) =
      some (.val (.word (w * 8))) := by
  simp [evalAt, evalHOLExact, evalListHOLExact, hw, valueIsWord, valueWord, panOpHOL]

/-- The copy offset has no modular wrap under the source length bound. -/
theorem stable_copy_mul_nat {F : Type} (s : PanSemStateFiniteExact 64 F)
    (w : BitVec 64) (hp : StableCopyInv s)
    (hw : s.locals.lookup (ofString "i") = some (.val (.word w)))
    (hi : locN s "i" < locN s "nl") :
    (w * 8).toNat = 8 * locN s "i" := by
  have hwi : locN s "i" = w.toNat := by simp [locN, hw]
  have hn := (stableLengthPost_length_bound s hp.1 hp.2.1).1
  rw [BitVec.toNat_mul]
  change (w.toNat * 8) % 2 ^ 64 = 8 * locN s "i"
  rw [Nat.mod_eq_of_lt (by omega), ← hwi, Nat.mul_comm]

/-- Identify the evaluated offset directly with the natural copy index. -/
theorem stable_copy_offset_eval {F : Type} (s : PanSemStateFiniteExact 64 F)
    (w : BitVec 64) (hp : StableCopyInv s)
    (hw : s.locals.lookup (ofString "i") = some (.val (.word w)))
    (hi : locN s "i" < locN s "nl") :
    evalAt s (.panop .mul [.var .local (ofString "i"), .const 8]) =
      some (.val (.word (BitVec.ofNat 64 (8 * locN s "i")))) := by
  rw [stable_copy_mul_eval s w hw]
  have he : w * 8 = BitVec.ofNat 64 (8 * locN s "i") := by
    rw [← stable_copy_mul_nat s w hp hw hi]
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [he]

/-- Evaluate the source address used by the copy load without modular wrap. -/
theorem stable_copy_source_address_eval {F : Type} (s : PanSemStateFiniteExact 64 F)
    (w p : BitVec 64) (hp : StableCopyInv s)
    (hw : s.locals.lookup (ofString "i") = some (.val (.word w)))
    (hl : s.locals.lookup (ofString "lp") = some (.val (.word p)))
    (hi : locN s "i" < locN s "nl") :
    evalAt s (.op .add [.var .local (ofString "lp"),
      .panop .mul [.var .local (ofString "i"), .const 8]]) =
      some (.val (.word (BitVec.ofNat 64 (locN s "lp" + 8 * locN s "i")))) := by
  have hpn : locN s "lp" = p.toNat := by simp [locN, hl]
  have hpw : p = BitVec.ofNat 64 (locN s "lp") := by
    rw [hpn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hoff := stable_copy_offset_eval s w hp hw hi
  simp only [evalAt, evalHOLExact, evalListHOLExact] at hoff ⊢
  rw [hl, hoff]
  simp only [valueIsWord, valueWord, List.all, List.map, Option.map,
    Bool.and_self, ↓reduceIte, wordOpHOL, wordOp, List.foldr]
  have he := (stableCopyInv_address_words s hp hi).1
  rw [hpw]
  rw [← he, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  simp

/-- Evaluate the destination address of the actual stable-copy store. -/
theorem stable_copy_destination_address_eval {F : Type} (s : PanSemStateFiniteExact 64 F)
    (w p : BitVec 64) (hp : StableCopyInv s)
    (hw : s.locals.lookup (ofString "i") = some (.val (.word w)))
    (hl : s.locals.lookup (ofString "stable_lp") = some (.val (.word p)))
    (hptr : p.toNat = memW s (locN s "stable_logs"))
    (hi : locN s "i" < locN s "nl") :
    evalAt s (.op .add [.var .local (ofString "stable_lp"),
      .panop .mul [.var .local (ofString "i"), .const 8]]) =
      some (.val (.word (BitVec.ofNat 64 (memW s (locN s "stable_logs") + 8 * locN s "i")))) := by
  have hpw : p = BitVec.ofNat 64 (memW s (locN s "stable_logs")) := by
    rw [← hptr, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hoff := stable_copy_offset_eval s w hp hw hi
  simp only [evalAt, evalHOLExact, evalListHOLExact] at hoff ⊢
  rw [hl, hoff]
  simp only [valueIsWord, valueWord, List.all, List.map, Option.map,
    Bool.and_self, ↓reduceIte, wordOpHOL, wordOp, List.foldr]
  have he := (stableCopyInv_address_words s hp hi).2
  rw [hpw]
  rw [← he, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  simp

/-- The copy source load returns the word at the indexed source cell. -/
theorem stable_copy_source_load_eval {F : Type} (s : PanSemStateFiniteExact 64 F)
    (w p : BitVec 64) (hp : StableCopyInv s)
    (hw : s.locals.lookup (ofString "i") = some (.val (.word w)))
    (hl : s.locals.lookup (ofString "lp") = some (.val (.word p)))
    (hi : locN s "i" < locN s "nl") :
    evalAt s phase4LogCopySrc = some (.val (.word
      (BitVec.ofNat 64 (memW s (locN s "lp" + 8 * locN s "i"))))) := by
  have he := stable_copy_source_address_eval s w p hp hw hl hi
  obtain ⟨v, hd, hm⟩ := (stableCopyInv_source_word s hp hi).1
  have hn : memW s (locN s "lp" + 8 * locN s "i") = v.toNat := by
    simp [memW, hm]
  unfold phase4LogCopySrc
  simp only [evalAt, evalHOLExact, evalListHOLExact] at he ⊢
  rw [he]
  simp [valueIsWord, valueWord, memLoadHOLExact, hd, hm, hn,
    BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- Loading the stable header yields the backing-pointer operand for copy setup. -/
theorem stable_backing_load_eval {F : Type} (s : PanSemStateFiniteExact 64 F)
    (w : BitVec 64)
    (hw : s.locals.lookup (ofString "stable_logs") = some (.val (.word w)))
    (hp : WordAt s (locN s "stable_logs")) :
    evalAt s (.load .one (.var .local (ofString "stable_logs"))) =
      some (.val (.word (BitVec.ofNat 64 (memW s (locN s "stable_logs"))))) := by
  have hl : locN s "stable_logs" = w.toNat := by simp [locN, hw]
  obtain ⟨v, hd, hm⟩ := hp
  have hn : memW s (locN s "stable_logs") = v.toNat := by simp [memW, hm]
  rw [hl] at hd hm
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at hd hm
  simp [evalAt, evalHOLExact, hw, valueIsWord, valueWord, memLoadHOLExact,
    hd, hm, hn, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The concrete backing load initializes its local with the header's word. -/
theorem stable_backing_load_local {F : Type} (s : PanSemStateFiniteExact 64 F)
    (w : BitVec 64) (v : ValueHOL 64)
    (hw : s.locals.lookup (ofString "stable_logs") = some (.val (.word w)))
    (hp : WordAt s (locN s "stable_logs"))
    (he : evalAt s (.load .one (.var .local (ofString "stable_logs"))) = some v) :
    ∃ q : BitVec 64,
      (setVarHOLFinite (ofString "stable_lp") v s).locals.lookup
        (ofString "stable_lp") = some (.val (.word q)) ∧
      q.toNat = memW s (locN s "stable_logs") := by
  have hv := stable_backing_load_eval s w hw hp
  rw [he] at hv
  have hv' := Option.some.inj hv
  subst v
  obtain ⟨q, hd, hm⟩ := hp
  have hn : memW s (locN s "stable_logs") = q.toNat := by simp [memW, hm]
  refine ⟨q, ?_, hn.symm⟩
  simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hn]

/-- Backing initialization retains both source operands required by the loop. -/
theorem stable_backing_load_operands {F : Type} (s : PanSemStateFiniteExact 64 F)
    (w n p : BitVec 64) (v : ValueHOL 64)
    (hw : s.locals.lookup (ofString "stable_logs") = some (.val (.word w)))
    (hn : s.locals.lookup (ofString "nl") = some (.val (.word n)))
    (hl : s.locals.lookup (ofString "lp") = some (.val (.word p)))
    (hp : WordAt s (locN s "stable_logs"))
    (he : evalAt s (.load .one (.var .local (ofString "stable_logs"))) = some v) :
    let t := setVarHOLFinite (ofString "stable_lp") v s
    t.locals.lookup (ofString "nl") = some (.val (.word n)) ∧
    t.locals.lookup (ofString "lp") = some (.val (.word p)) ∧
    ∃ q : BitVec 64, t.locals.lookup (ofString "stable_lp") = some (.val (.word q)) ∧
      q.toNat = memW t (locN t "stable_logs") := by
  obtain ⟨q, hq, hd⟩ := stable_backing_load_local s w v hw hp he
  refine ⟨?_, ?_, q, hq, ?_⟩
  · simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, ofString] using hn
  · simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, ofString] using hl
  · simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, ofString, memW, locN] using hd

/-- A successful semantic copy store writes the indexed source value. -/
theorem stable_copy_store_value {F : Type} (s : PanSemStateFiniteExact 64 F)
    (mem' : BitVec 64 → HolWordLab 64) (w p : BitVec 64)
    (hp : StableCopyInv s)
    (hw : s.locals.lookup (ofString "i") = some (.val (.word w)))
    (hl : s.locals.lookup (ofString "lp") = some (.val (.word p)))
    (hi : locN s "i" < locN s "nl") (v : ValueHOL 64)
    (hv : evalAt s phase4LogCopySrc = some v)
    (he : mem' (BitVec.ofNat 64
      (memW s (locN s "stable_logs") + 8 * locN s "i")) =
      .word (BitVec.ofNat 64 (memW s (locN s "lp" + 8 * locN s "i")))) :
    v = .val (.word (BitVec.ofNat 64
      (memW s (memW s (locN s "logs") + 8 * locN s "i")))) ∧
    memW {s with memory := mem'}
      (memW s (locN s "stable_logs") + 8 * locN s "i") =
      memW s (memW s (locN s "logs") + 8 * locN s "i") := by
  have hv' := stable_copy_source_load_eval s w p hp hw hl hi
  have hn : memW s (locN s "lp" + 8 * locN s "i") < 2 ^ 64 := by
    unfold memW
    cases s.memory (BitVec.ofNat 64 (locN s "lp" + 8 * locN s "i")) with
    | word a => exact a.isLt
  constructor
  · rw [hv] at hv'
    rw [hp.1.2.2.2.2.1] at hv'
    exact Option.some.inj hv'
  · change (match mem' _ with | .word a => a.toNat) = _
    rw [he]
    dsimp only
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, hp.1.2.2.2.2.1]

/-- The stored word is exactly the source pointer, with no truncation. -/
theorem stable_copy_written_value {F : Type} (s : PanSemStateFiniteExact 64 F)
    (mem' : BitVec 64 → HolWordLab 64) (hp : StableCopyInv s)
    (hi : locN s "i" < locN s "nl")
    (he : mem' (BitVec.ofNat 64
      (memW s (locN s "stable_logs") + 8 * locN s "i")) =
      .word (BitVec.ofNat 64 (memW s (locN s "lp" + 8 * locN s "i")))) :
    memW {s with memory := mem'}
        (memW s (locN s "stable_logs") + 8 * locN s "i") =
      memW s (memW s (locN s "logs") + 8 * locN s "i") := by
  obtain ⟨w, _, hw⟩ := (stableCopyInv_source_word s hp hi).1
  have hv : memW s (locN s "lp" + 8 * locN s "i") = w.toNat := by
    simp [memW, hw]
  have hdest : memW {s with memory := mem'}
      (memW s (locN s "stable_logs") + 8 * locN s "i") = w.toNat := by
    change (mem' (BitVec.ofNat 64
      (memW s (locN s "stable_logs") + 8 * locN s "i"))).1.toNat = w.toNat
    rw [he, hv]
    simp
  rw [hdest, ← hv, hp.1.2.2.2.2.1]

/-- Extract the value and frame facts from the actual one-word copy store. -/
theorem stable_copy_store_semantics {F : Type} (s : PanSemStateFiniteExact 64 F)
    (mem' : BitVec 64 → HolWordLab 64) (w p : BitVec 64)
    (hp : StableCopyInv s)
    (hw : s.locals.lookup (ofString "i") = some (.val (.word w)))
    (hl : s.locals.lookup (ofString "lp") = some (.val (.word p)))
    (hi : locN s "i" < locN s "nl") (v : ValueHOL 64)
    (hv : evalAt s phase4LogCopySrc = some v)
    (hst : @panMemStoresHOL 64 _
      (BitVec.ofNat 64 (memW s (locN s "stable_logs") + 8 * locN s "i"))
      (flattenHOL v) s.memaddrs
      (fun a => Classical.propDecidable (s.memaddrs a)) s.memory = some mem') :
    s.memaddrs (BitVec.ofNat 64
      (memW s (locN s "stable_logs") + 8 * locN s "i")) ∧
    memW {s with memory := mem'}
      (memW s (locN s "stable_logs") + 8 * locN s "i") =
      memW s (memW s (locN s "logs") + 8 * locN s "i") ∧
    ∀ a, a ≠ BitVec.ofNat 64
      (memW s (locN s "stable_logs") + 8 * locN s "i") → mem' a = s.memory a := by
  have hv' := stable_copy_source_load_eval s w p hp hw hl hi
  rw [hv] at hv'
  have heq := Option.some.inj hv'
  subst v
  obtain ⟨hd, he, hm⟩ := R13Shards.panMemStoresHOL_word_spec
    (by simpa only [flattenHOL] using hst)
  exact ⟨hd, stable_copy_written_value s mem' hp hi he, hm⟩

/-- Operand shapes and allocation separation required by the copy store. -/
def StableCopyStorePre : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => StableCopyInv s ∧ locN s "i" < locN s "nl" ∧
    (∃ w p q : BitVec 64,
      s.locals.lookup (ofString "i") = some (.val (.word w)) ∧
      s.locals.lookup (ofString "lp") = some (.val (.word p)) ∧
      s.locals.lookup (ofString "stable_lp") = some (.val (.word q)) ∧
      q.toNat = memW s (locN s "stable_logs")) ∧
    ∃ S Nd, WorldTypedWith s S Nd ∧ LogsLiveOwned s S Nd (locN s "logs") ∧
      (∀ o ∈ worldOwned s S Nd,
        Disj (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") o) ∧
      Disj (locN s "logs", 24)
        (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
      Disj (locN s "stable_logs", 24)
        (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
      Disj (memW s (locN s "logs"), 8 * memW s (locN s "logs" + 8))
        (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
      ∀ j, j < memW s (locN s "logs" + 8) →
        Disj (memW s (memW s (locN s "logs") + 8 * j), 40)
          (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap")

/-- Framed source pointers retain record/backing separation after a copy
write. This supplies the record-separation premise for the next iteration. -/
theorem stable_copy_record_separation {F : Type} (s : PanSemStateFiniteExact 64 F)
    (mem' : BitVec 64 → HolWordLab 64)
    (hs : memW {s with memory := mem'} (locN s "logs") = memW s (locN s "logs"))
    (hn : memW {s with memory := mem'} (locN s "logs" + 8) =
      memW s (locN s "logs" + 8))
    (hd : memW {s with memory := mem'} (locN s "stable_logs") =
      memW s (locN s "stable_logs"))
    (ha : ∀ j, j < memW s (locN s "logs" + 8) →
      memW {s with memory := mem'} (memW s (locN s "logs") + 8 * j) =
        memW s (memW s (locN s "logs") + 8 * j))
    (he : ∀ j, j < memW s (locN s "logs" + 8) →
      Disj (memW s (memW s (locN s "logs") + 8 * j), 40)
        (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap")) :
    let t := {s with memory := mem'}
    ∀ j, j < memW t (locN t "logs" + 8) →
      Disj (memW t (memW t (locN t "logs") + 8 * j), 40)
        (memW t (locN t "stable_logs"), 8 * locN t "stable_log_cap") := by
  dsimp only
  intro j hj
  change j < memW {s with memory := mem'} (locN s "logs" + 8) at hj
  rw [hn] at hj
  change Disj (memW {s with memory := mem'}
    (memW {s with memory := mem'} (locN s "logs") + 8 * j), 40)
    (memW {s with memory := mem'} (locN s "stable_logs"), 8 * locN s "stable_log_cap")
  rw [hs, hd, ha j hj]
  exact he j hj

/-- Carry source-record separation through the stable length update using
the source backing's allocation and disjointness from the stable header. -/
theorem stable_length_record_separation {F : Type} (s : PanSemStateFiniteExact 64 F)
    (mem' : BitVec 64 → HolWordLab 64)
    (hA : ArenaOK s) (hh : Allocated s (locN s "stable_logs", 24))
    (ha : Allocated s (memW s (locN s "logs"), 8 * memW s (locN s "logs" + 8)))
    (hal : memW s (locN s "logs") % 8 = 0)
    (hdisj : Disj (memW s (locN s "logs"), 8 * memW s (locN s "logs" + 8))
      (locN s "stable_logs", 24))
    (hm : ∀ a, a ≠ BitVec.ofNat 64 (locN s "stable_logs" + 8) → mem' a = s.memory a)
    (hs : memW {s with memory := mem'} (locN s "logs") = memW s (locN s "logs"))
    (hn : memW {s with memory := mem'} (locN s "logs" + 8) = memW s (locN s "logs" + 8))
    (hd : memW {s with memory := mem'} (locN s "stable_logs") = memW s (locN s "stable_logs"))
    (he : ∀ j, j < memW s (locN s "logs" + 8) →
      Disj (memW s (memW s (locN s "logs") + 8 * j), 40)
        (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap")) :
    let t := {s with memory := mem'}
    ∀ j, j < memW t (locN t "logs" + 8) →
      Disj (memW t (memW t (locN t "logs") + 8 * j), 40)
        (memW t (locN t "stable_logs"), 8 * locN t "stable_log_cap") := by
  exact stable_copy_record_separation s mem' hs hn hd
    (stable_length_source_cells s mem' _ _ hA hh ha hal hdisj hm) he

/-- The length-store contract preserves record/backing separation with no
additional source-cell framing obligations. -/
theorem stableLengthPre_record_separation {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableLengthPre s) (mem' : BitVec 64 → HolWordLab 64)
    (hx : s.memaddrs (BitVec.ofNat 64 (locN s "stable_logs" + 8)))
    (hm : ∀ a, a ≠ BitVec.ofNat 64 (locN s "stable_logs" + 8) → mem' a = s.memory a)
    (he : ∀ j, j < memW s (locN s "logs" + 8) →
      Disj (memW s (memW s (locN s "logs") + 8 * j), 40)
        (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap")) :
    let t := {s with memory := mem'}
    ∀ j, j < memW t (locN t "logs" + 8) →
      Disj (memW t (memW t (locN t "logs") + 8 * j), 40)
        (memW t (locN t "stable_logs"), 8 * locN t "stable_log_cap") := by
  obtain ⟨S, Nd, hW, ho, hs, hh, ha, hr⟩ := hp.2.2.2.2
  have hf := stable_length_store_source s hp.1 hp.2.1 S Nd hW ho hs hh ha hr hx mem' hm
  have hd := (stable_length_store_header_unchanged s hp.1.1.1.1.1.1.1.1.1.1.2
    hp.2.1 mem' hm).1
  exact stable_copy_record_separation s mem' hf.2.2.2.2.2.1 hf.2.2.2.2.2.2 hd
    (stableLengthPre_source_cells s hp mem' hm) he

/-- Both header/backing separation facts survive the stable length update. -/
theorem stableLengthPre_headers_separation {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableLengthPre s) (mem' : BitVec 64 → HolWordLab 64)
    (hm : ∀ a, a ≠ BitVec.ofNat 64 (locN s "stable_logs" + 8) → mem' a = s.memory a)
    (hs : Disj (locN s "logs", 24)
      (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap"))
    (hd : Disj (locN s "stable_logs", 24)
      (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap")) :
    let t := {s with memory := mem'}
    Disj (locN t "logs", 24)
      (memW t (locN t "stable_logs"), 8 * locN t "stable_log_cap") ∧
    Disj (locN t "stable_logs", 24)
      (memW t (locN t "stable_logs"), 8 * locN t "stable_log_cap") := by
  have hb := (stable_length_store_header_unchanged s hp.1.1.1.1.1.1.1.1.1.1.2
    hp.2.1 mem' hm).1
  dsimp only
  change Disj (locN s "logs", 24)
    (memW {s with memory := mem'} (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
    Disj (locN s "stable_logs", 24)
    (memW {s with memory := mem'} (locN s "stable_logs"), 8 * locN s "stable_log_cap")
  rw [hb]
  exact ⟨hs, hd⟩

/-- Source-array/backing separation survives the stable length update. -/
theorem stableLengthPre_array_separation {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableLengthPre s) (mem' : BitVec 64 → HolWordLab 64)
    (hx : s.memaddrs (BitVec.ofNat 64 (locN s "stable_logs" + 8)))
    (hm : ∀ a, a ≠ BitVec.ofNat 64 (locN s "stable_logs" + 8) → mem' a = s.memory a)
    (hd : Disj (memW s (locN s "logs"), 8 * memW s (locN s "logs" + 8))
      (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap")) :
    let t := {s with memory := mem'}
    Disj (memW t (locN t "logs"), 8 * memW t (locN t "logs" + 8))
      (memW t (locN t "stable_logs"), 8 * locN t "stable_log_cap") := by
  obtain ⟨S, Nd, hW, ho, hs, hh, ha, hr⟩ := hp.2.2.2.2
  have hf := stable_length_store_source s hp.1 hp.2.1 S Nd hW ho hs hh ha hr hx mem' hm
  have hb := (stable_length_store_header_unchanged s hp.1.1.1.1.1.1.1.1.1.1.2
    hp.2.1 mem' hm).1
  dsimp only
  change Disj (memW {s with memory := mem'} (locN s "logs"),
    8 * memW {s with memory := mem'} (locN s "logs" + 8))
    (memW {s with memory := mem'} (locN s "stable_logs"), 8 * locN s "stable_log_cap")
  rw [hf.2.2.2.2.2.1, hf.2.2.2.2.2.2, hb]
  exact hd

/-- Framing the destination header and world footprint retains separation
from every world-owned interval after the copy store. -/
theorem stable_copy_world_separation {F : Type} (s : PanSemStateFiniteExact 64 F)
    (mem' : BitVec 64 → HolWordLab 64) (S Nd : List Nat)
    (hd : memW {s with memory := mem'} (locN s "stable_logs") =
      memW s (locN s "stable_logs"))
    (hw : worldOwned {s with memory := mem'} S Nd = worldOwned s S Nd)
    (hp : ∀ o ∈ worldOwned s S Nd,
      Disj (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") o) :
    let t := {s with memory := mem'}
    ∀ o ∈ worldOwned t S Nd,
      Disj (memW t (locN t "stable_logs"), 8 * locN t "stable_log_cap") o := by
  dsimp only
  intro o ho
  rw [hw] at ho
  change Disj (memW {s with memory := mem'} (locN s "stable_logs"),
    8 * locN s "stable_log_cap") o
  rw [hd]
  exact hp o ho

/-- Preserve backing/world separation across the length write using the
same ownership witnesses as the length-store contract. -/
theorem stableLengthPre_world_separation {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableLengthPre s) (mem' : BitVec 64 → HolWordLab 64)
    (hx : s.memaddrs (BitVec.ofNat 64 (locN s "stable_logs" + 8)))
    (hm : ∀ a, a ≠ BitVec.ofNat 64 (locN s "stable_logs" + 8) → mem' a = s.memory a)
    (S Nd : List Nat) (hW : WorldTypedWith s S Nd)
    (ho : LogsLiveOwned s S Nd (locN s "logs"))
    (hs : ∀ o ∈ worldOwned s S Nd, Disj (locN s "stable_logs", 24) o)
    (hb : ∀ o ∈ worldOwned s S Nd,
      Disj (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") o) :
    let t := {s with memory := mem'}
    WorldTypedWith t S Nd ∧ LogsLiveOwned t S Nd (locN t "logs") ∧
      ∀ o ∈ worldOwned t S Nd,
        Disj (memW t (locN t "stable_logs"), 8 * locN t "stable_log_cap") o := by
  obtain ⟨_, _, _, _, _, hh, ha, hr⟩ := hp.2.2.2.2
  have hf := stable_length_store_source s hp.1 hp.2.1 S Nd hW ho hs hh ha hr hx mem' hm
  have hd := (stable_length_store_header_unchanged s hp.1.1.1.1.1.1.1.1.1.1.2
    hp.2.1 mem' hm).1
  exact ⟨hf.1, hf.2.2.2.2.1, stable_copy_world_separation s mem' S Nd hd hf.2.1 hb⟩

/-- Package the spatial obligations needed at copy entry independently of
the counter and operand locals. -/
def StableCopySpatial : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ∃ S Nd, WorldTypedWith s S Nd ∧ LogsLiveOwned s S Nd (locN s "logs") ∧
    (∀ o ∈ worldOwned s S Nd,
      Disj (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") o) ∧
    Disj (locN s "logs", 24)
      (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
    Disj (locN s "stable_logs", 24)
      (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
    Disj (memW s (locN s "logs"), 8 * memW s (locN s "logs" + 8))
      (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
    ∀ j, j < memW s (locN s "logs" + 8) →
      Disj (memW s (memW s (locN s "logs") + 8 * j), 40)
        (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap")

/-- A coherent world witness retains both header and backing separation. -/
def StableCopyOwnedFrame : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ∃ S Nd, WorldTypedWith s S Nd ∧
    LogsLiveOwned s S Nd (locN s "logs") ∧
    (∀ o ∈ worldOwned s S Nd, Disj (locN s "stable_logs", 24) o) ∧
    ∀ o ∈ worldOwned s S Nd,
      Disj (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") o

/-- Updating the stable length retains the coherent ownership witness. -/
theorem stableCopyOwnedFrame_length_store {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableLengthPre s) (mem' : BitVec 64 → HolWordLab 64)
    (hx : s.memaddrs (BitVec.ofNat 64 (locN s "stable_logs" + 8)))
    (hm : ∀ a, a ≠ BitVec.ofNat 64 (locN s "stable_logs" + 8) → mem' a = s.memory a)
    (hframe : StableCopyOwnedFrame s) :
    StableCopyOwnedFrame {s with memory := mem'} := by
  obtain ⟨S, Nd, hW, ho, hs, hb⟩ := hframe
  obtain ⟨_, _, _, _, _, hh, ha, hr⟩ := hp.2.2.2.2
  have hf := stable_length_store_source s hp.1 hp.2.1 S Nd hW ho hs hh ha hr hx mem' hm
  have hd := (stable_length_store_header_unchanged s hp.1.1.1.1.1.1.1.1.1.1.2
    hp.2.1 mem' hm).1
  refine ⟨S, Nd, hf.1, hf.2.2.2.2.1, ?_,
    stable_copy_world_separation s mem' S Nd hd hf.2.1 hb⟩
  intro o hmem
  rw [hf.2.1] at hmem
  exact hs o hmem

/-- A separated copy write preserves the coherent header/backing ownership frame. -/
theorem stableCopyOwnedFrame_store {F : Type} (s : PanSemStateFiniteExact 64 F)
    (mem' : BitVec 64 → HolWordLab 64) (hp : StableCopyInv s)
    (hf : StableCopyOwnedFrame s) (hsp : StableCopySpatial s)
    (hi : locN s "i" < locN s "nl")
    (hx : s.memaddrs (BitVec.ofNat 64
      (memW s (locN s "stable_logs") + 8 * locN s "i")))
    (hm : ∀ a, a ≠ BitVec.ofNat 64
      (memW s (locN s "stable_logs") + 8 * locN s "i") → mem' a = s.memory a) :
    StableCopyOwnedFrame {s with memory := mem'} := by
  obtain ⟨S, Nd, hW, ho, hh, hb⟩ := hf
  obtain ⟨_, _, _, _, _, hsrc, hdst, harr, hentry⟩ := hsp
  obtain ⟨hW', hw', _⟩ := stableCopyInv_world_preserved s mem' hp hi S Nd hW hb hx hm
  have hg : GuestInv {s with memory := mem'} :=
    guestInv_congr (s := s) rfl rfl rfl rfl hp.1.1.1.1.1
  have ho' := (stableCopyInv_logs_preserved s mem' hp hi S Nd ho hg hw'
    hsrc harr hentry hm).2
  have hd0 := (stableCopyInv_header_unhit s mem' hp hi _
    hp.2.2.2.1 hp.2.2.1.1 hdst hm).1
  refine ⟨S, Nd, hW', ho', ?_, ?_⟩
  · intro o ho
    rw [hw'] at ho
    exact hh o ho
  · intro o ho
    rw [hw'] at ho
    change Disj (memW {s with memory := mem'} (locN s "stable_logs"),
      8 * locN s "stable_log_cap") o
    rw [hd0]
    exact hb o ho

/-- The concrete indexed store retains the coherent ownership frame. -/
theorem hoare_stableCopy_store_ownedFrame :
    Hoare (fun s => StableCopyStorePre s ∧ StableCopyOwnedFrame s)
      (.store (.op .add [.var .local (ofString "stable_lp"),
        .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
      (fun r t => r = none → StableCopyOwnedFrame t) := by
  refine R13Shards.Hoare.store_fall fun s x v mem' hp hx hv hst => ?_
  obtain ⟨⟨hinv, hi, ⟨w, p, q, hw, hl, hq, hptr⟩,
    S, Nd, hW, ho, hworld, hh, hd, ha, he⟩, hf⟩ := hp
  have hx' := stable_copy_destination_address_eval s w q hinv hw hq hptr hi
  rw [hx] at hx'
  have hxe : x = BitVec.ofNat 64
      (memW s (locN s "stable_logs") + 8 * locN s "i") := by
    simpa using Option.some.inj hx'
  subst x
  obtain ⟨hdom, _, hm⟩ := stable_copy_store_semantics s mem' w p hinv hw hl hi v hv hst
  exact stableCopyOwnedFrame_store s mem' hinv hf
    ⟨S, Nd, hW, ho, hworld, hh, hd, ha, he⟩ hi hdom hm

/-- Local initialization and clock changes preserve the coherent ownership frame. -/
theorem stableCopyOwnedFrame_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat)
    (hl : locals.lookup (ofString "logs") = s.locals.lookup (ofString "logs"))
    (hs : locals.lookup (ofString "stable_logs") = s.locals.lookup (ofString "stable_logs"))
    (hc : locals.lookup (ofString "stable_log_cap") = s.locals.lookup (ofString "stable_log_cap"))
    (hp : StableCopyOwnedFrame s) :
    StableCopyOwnedFrame {s with locals := locals, clock := k} := by
  obtain ⟨S, Nd, hW, ho, hh, hb⟩ := hp
  have el := locN_congr s locals k "logs" hl
  have es := locN_congr s locals k "stable_logs" hs
  have ec := locN_congr s locals k "stable_log_cap" hc
  refine ⟨S, Nd, (R13Shards.worldTypedWith_with_locals s locals k S Nd).mpr hW, ?_⟩
  simp only [el, es, ec]
  exact ⟨ho, hh, hb⟩

/-- Assignments to temporary locals retain the coherent ownership frame. -/
theorem hoare_stableCopyOwnedFrame_assign (name : MlS) (e : ExpHOL 64)
    (hl : name ≠ ofString "logs") (hs : name ≠ ofString "stable_logs")
    (hc : name ≠ ofString "stable_log_cap") :
    Hoare StableCopyOwnedFrame (.assign .local name e)
      (fun r t => r = none → StableCopyOwnedFrame t) := by
  apply Hoare.assign
  · intro F s v hp hv _
    apply stableCopyOwnedFrame_with_locals s _ s.clock _ _ _ hp
    all_goals simp [HolFiniteMapExact.lookup_update, FUPDATE, hl, hs, hc]
  · intro F s hp hr
    cases hr

/-- The coherent ownership frame strengthens the copy exit postcondition. -/
theorem stableCopyOwnedFrame_exit {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableCopyInv s) (hf : StableCopyOwnedFrame s)
    (hexit : locN s "nl" ≤ locN s "i") :
    PtxReceiptsDone s ∧ LogsWorldOwned s (locN s "stable_logs") := by
  obtain ⟨S, Nd, hW, ho, hh, hb⟩ := hf
  exact ⟨stableCopyInv_exit s hp hexit,
    S, Nd, hW, stableCopyInv_exit_owned_of_capacity s hp hexit ho hh hb⟩

/-- Counter and backing-pointer local initialization preserve spatial facts. -/
theorem stableCopySpatial_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat)
    (hl : locals.lookup (ofString "logs") = s.locals.lookup (ofString "logs"))
    (hs : locals.lookup (ofString "stable_logs") = s.locals.lookup (ofString "stable_logs"))
    (hc : locals.lookup (ofString "stable_log_cap") = s.locals.lookup (ofString "stable_log_cap"))
    (hp : StableCopySpatial s) : StableCopySpatial {s with locals := locals, clock := k} := by
  obtain ⟨S, Nd, hW, ho, hw, hh, hd, ha, he⟩ := hp
  have el := locN_congr s locals k "logs" hl
  have es := locN_congr s locals k "stable_logs" hs
  have ec := locN_congr s locals k "stable_log_cap" hc
  refine ⟨S, Nd, (R13Shards.worldTypedWith_with_locals s locals k S Nd).mpr hW, ?_⟩
  simp only [el, es, ec]
  exact ⟨ho, hw, hh, hd, ha, he⟩

/-- Updating a local other than the three spatial roots preserves separation. -/
theorem stableCopySpatial_setVar {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name : MlS) (v : ValueHOL 64)
    (hl : name ≠ ofString "logs") (hs : name ≠ ofString "stable_logs")
    (hc : name ≠ ofString "stable_log_cap") (hp : StableCopySpatial s) :
    StableCopySpatial (setVarHOLFinite name v s) := by
  apply stableCopySpatial_with_locals s _ s.clock _ _ _ hp
  all_goals simp [HolFiniteMapExact.lookup_update, FUPDATE, hl, hs, hc]

/-- Local assignments, including the stable backing load, frame the spatial
contract whenever they leave its three root locals unchanged. -/
theorem hoare_stableCopySpatial_assign (name : MlS) (e : ExpHOL 64)
    (hl : name ≠ ofString "logs") (hs : name ≠ ofString "stable_logs")
    (hc : name ≠ ofString "stable_log_cap") :
    Hoare StableCopySpatial (.assign .local name e)
      (fun r t => r = none → StableCopySpatial t) := by
  apply Hoare.assign
  · intro F s v hp hv _
    exact stableCopySpatial_setVar s name v hl hs hc hp
  · intro F s hp hr
    cases hr

/-- The concrete backing load retains spatial facts and installs the exact
word-valued destination pointer used by the copy loop. -/
theorem hoare_stable_backing_load :
    Hoare (fun s => StableCopySpatial s ∧ WordAt s (locN s "stable_logs") ∧
      ∃ w : BitVec 64, s.locals.lookup (ofString "stable_logs") = some (.val (.word w)))
      (.assign .local (ofString "stable_lp")
        (.load .one (.var .local (ofString "stable_logs"))))
      (fun r t => r = none → StableCopySpatial t ∧
        ∃ q : BitVec 64, t.locals.lookup (ofString "stable_lp") = some (.val (.word q)) ∧
          q.toNat = memW t (locN t "stable_logs")) := by
  apply Hoare.assign
  · intro F s v hp hv _
    obtain ⟨hs, hw, w, hl⟩ := hp
    have he := stable_backing_load_eval s w hl hw
    change evalAt s (.load .one (.var .local (ofString "stable_logs"))) = some v at hv
    rw [hv] at he
    have hv' := Option.some.inj he
    subst v
    refine ⟨stableCopySpatial_setVar s _ _ (by decide) (by decide) (by decide) hs,
      BitVec.ofNat 64 (memW s (locN s "stable_logs")), ?_, ?_⟩
    · simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
    · simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, locN, memW, ofString]
  · intro F s hp hr
    cases hr

/-- All copy-entry spatial obligations survive the stable length write. -/
theorem stableLengthPre_spatial {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableLengthPre s) (mem' : BitVec 64 → HolWordLab 64)
    (hx : s.memaddrs (BitVec.ofNat 64 (locN s "stable_logs" + 8)))
    (hm : ∀ a, a ≠ BitVec.ofNat 64 (locN s "stable_logs" + 8) → mem' a = s.memory a)
    (hs : ∃ S Nd, WorldTypedWith s S Nd ∧ LogsLiveOwned s S Nd (locN s "logs") ∧
      (∀ o ∈ worldOwned s S Nd, Disj (locN s "stable_logs", 24) o) ∧
      (∀ o ∈ worldOwned s S Nd,
        Disj (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") o))
    (hh : Disj (locN s "logs", 24)
      (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap"))
    (hd : Disj (locN s "stable_logs", 24)
      (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap"))
    (ha : Disj (memW s (locN s "logs"), 8 * memW s (locN s "logs" + 8))
      (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap"))
    (he : ∀ j, j < memW s (locN s "logs" + 8) →
      Disj (memW s (memW s (locN s "logs") + 8 * j), 40)
        (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap")) :
    StableCopySpatial {s with memory := mem'} := by
  obtain ⟨S, Nd, hW, ho, hs, hb⟩ := hs
  obtain ⟨hW', ho', hb'⟩ := stableLengthPre_world_separation s hp mem' hx hm S Nd hW ho hs hb
  obtain ⟨hh', hd'⟩ := stableLengthPre_headers_separation s hp mem' hm hh hd
  exact ⟨S, Nd, hW', ho', hb', hh', hd',
    stableLengthPre_array_separation s hp mem' hx hm ha,
    stableLengthPre_record_separation s hp mem' hx hm he⟩

/-- Spatial framing for the concrete stable length store, retaining a coherent
world witness for both the header and its backing allocation. -/
theorem hoare_stable_length_spatial :
    Hoare (fun s => StableLengthPre s ∧
      (∃ S Nd, WorldTypedWith s S Nd ∧ LogsLiveOwned s S Nd (locN s "logs") ∧
        (∀ o ∈ worldOwned s S Nd, Disj (locN s "stable_logs", 24) o) ∧
        (∀ o ∈ worldOwned s S Nd,
          Disj (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") o)) ∧
      Disj (locN s "logs", 24)
        (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
      Disj (locN s "stable_logs", 24)
        (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
      Disj (memW s (locN s "logs"), 8 * memW s (locN s "logs" + 8))
        (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
      ∀ j, j < memW s (locN s "logs" + 8) →
        Disj (memW s (memW s (locN s "logs") + 8 * j), 40)
          (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap"))
      (.store (.op .add [.var .local (ofString "stable_logs"), .const 8])
        (.var .local (ofString "nl")))
      (fun r t => r = none → StableCopySpatial t) := by
  refine R13Shards.Hoare.store_fall fun s x v mem' hp hx hv hst => ?_
  obtain ⟨hp, hs, hh, hd, ha, he⟩ := hp
  have hlocal := hp.2.2.1
  have hnl := hp.2.2.2.1
  have hv' : v = .val (.word (BitVec.ofNat 64 (locN s "nl"))) := by
    change s.locals.lookup (ofString "nl") = some v at hv
    rw [hnl] at hv
    exact (Option.some.inj hv).symm
  subst v
  have hx' : x = BitVec.ofNat 64 (locN s "stable_logs" + 8) := by
    simp [evalAt, evalHOLExact, evalListHOLExact, hlocal, valueIsWord,
      valueWord, wordOpHOL, wordOp] at hx
    subst x
    apply BitVec.eq_of_toNat_eq
    have hb := stable_length_address_bound s hp.1.1.1.1.1.1.1.1.1.1.2 hp.2.1
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb.1] using hb.2
  subst x
  obtain ⟨hdom, hval, hm⟩ := R13Shards.panMemStoresHOL_word_spec
    (by simpa only [flattenHOL] using hst)
  exact stableLengthPre_spatial s hp mem' hdom hm hs hh hd ha he

/-- The concrete stable-length write preserves the coherent ownership frame. -/
theorem hoare_stable_length_ownedFrame :
    Hoare (fun s => StableLengthPre s ∧ StableCopyOwnedFrame s)
      (.store (.op .add [.var .local (ofString "stable_logs"), .const 8])
        (.var .local (ofString "nl")))
      (fun r t => r = none → StableCopyOwnedFrame t) := by
  refine R13Shards.Hoare.store_fall fun s x v mem' hp hx hv hst => ?_
  obtain ⟨hp, hf⟩ := hp
  have hlocal := hp.2.2.1
  have hnl := hp.2.2.2.1
  have hv' : v = .val (.word (BitVec.ofNat 64 (locN s "nl"))) := by
    change s.locals.lookup (ofString "nl") = some v at hv
    rw [hnl] at hv
    exact (Option.some.inj hv).symm
  subst v
  have hx' : x = BitVec.ofNat 64 (locN s "stable_logs" + 8) := by
    simp [evalAt, evalHOLExact, evalListHOLExact, hlocal, valueIsWord,
      valueWord, wordOpHOL, wordOp] at hx
    subst x
    apply BitVec.eq_of_toNat_eq
    have hb := stable_length_address_bound s hp.1.1.1.1.1.1.1.1.1.1.2 hp.2.1
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb.1] using hb.2
  subst x
  obtain ⟨hdom, _, hm⟩ := R13Shards.panMemStoresHOL_word_spec
    (by simpa only [flattenHOL] using hst)
  exact stableCopyOwnedFrame_length_store s hp mem' hdom hm hf

/-- Combine the length and spatial postconditions of the same concrete write. -/
theorem hoare_stable_length_joint :
    Hoare (fun s => StableLengthPre s ∧
      (∃ S Nd, WorldTypedWith s S Nd ∧ LogsLiveOwned s S Nd (locN s "logs") ∧
        (∀ o ∈ worldOwned s S Nd, Disj (locN s "stable_logs", 24) o) ∧
        (∀ o ∈ worldOwned s S Nd,
          Disj (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") o)) ∧
      Disj (locN s "logs", 24)
        (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
      Disj (locN s "stable_logs", 24)
        (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
      Disj (memW s (locN s "logs"), 8 * memW s (locN s "logs" + 8))
        (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
      ∀ j, j < memW s (locN s "logs" + 8) →
        Disj (memW s (memW s (locN s "logs") + 8 * j), 40)
          (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap"))
      (.store (.op .add [.var .local (ofString "stable_logs"), .const 8])
        (.var .local (ofString "nl")))
      (fun r t => r = none → StableLengthPost t ∧ StableCopySpatial t) := by
  constructor
  intro F s hc hp hnt hr
  exact ⟨hoare_stable_length_store.run s hc hp.1 hnt hr,
    hoare_stable_length_spatial.run s hc hp hnt hr⟩

/-- The actual length store retains all non-spatial copy-setup operands and
the readable stable header. -/
theorem hoare_stable_length_setup_frame :
    Hoare (fun s => StableLengthPre s ∧ locN s "logs" ≠ 0 ∧
      WordsOK s (locN s "stable_logs", 24) ∧
      locN s "nl" ≤ locN s "stable_log_cap" ∧
      ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p)))
      (.store (.op .add [.var .local (ofString "stable_logs"), .const 8])
        (.var .local (ofString "nl")))
      (fun r t => r = none → locN t "logs" ≠ 0 ∧
        WordsOK t (locN t "stable_logs", 24) ∧ Allocated t (locN t "stable_logs", 24) ∧
        locN t "nl" ≤ locN t "stable_log_cap" ∧ WordAt t (locN t "stable_logs") ∧
        ∃ n p w : BitVec 64,
          t.locals.lookup (ofString "nl") = some (.val (.word n)) ∧
          t.locals.lookup (ofString "lp") = some (.val (.word p)) ∧
          t.locals.lookup (ofString "stable_logs") = some (.val (.word w))) := by
  refine R13Shards.Hoare.store_fall fun s x v mem' hp hx hv hst => ?_
  obtain ⟨hp, hz, hh, hc, p, hl⟩ := hp
  have hlocal := hp.2.2.1
  have hnl := hp.2.2.2.1
  have hv' : v = .val (.word (BitVec.ofNat 64 (locN s "nl"))) := by
    change s.locals.lookup (ofString "nl") = some v at hv
    rw [hnl] at hv
    exact (Option.some.inj hv).symm
  subst v
  have hx' : x = BitVec.ofNat 64 (locN s "stable_logs" + 8) := by
    simp [evalAt, evalHOLExact, evalListHOLExact, hlocal, valueIsWord,
      valueWord, wordOpHOL, wordOp] at hx
    subst x
    apply BitVec.eq_of_toNat_eq
    have hb := stable_length_address_bound s hp.1.1.1.1.1.1.1.1.1.1.2 hp.2.1
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb.1] using hb.2
  subst x
  obtain ⟨hdom, he, hm⟩ := R13Shards.panMemStoresHOL_word_spec
    (by simpa only [flattenHOL] using hst)
  obtain ⟨hh', ha', hw'⟩ := stable_length_store_header_ready s mem' _ he hm hh hp.2.1
  exact ⟨hz, hh', ha', hc, hw', stableLengthPre_memory_operands s hp mem' p hl⟩

/-- The length store establishes the complete backing-load setup contract. -/
theorem hoare_stable_length_copy_ready :
    Hoare (fun s => (StableLengthPre s ∧
      (∃ S Nd, WorldTypedWith s S Nd ∧ LogsLiveOwned s S Nd (locN s "logs") ∧
        (∀ o ∈ worldOwned s S Nd, Disj (locN s "stable_logs", 24) o) ∧
        (∀ o ∈ worldOwned s S Nd,
          Disj (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") o)) ∧
      Disj (locN s "logs", 24)
        (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
      Disj (locN s "stable_logs", 24)
        (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
      Disj (memW s (locN s "logs"), 8 * memW s (locN s "logs" + 8))
        (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
      ∀ j, j < memW s (locN s "logs" + 8) →
        Disj (memW s (memW s (locN s "logs") + 8 * j), 40)
          (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap")) ∧
      locN s "logs" ≠ 0 ∧ WordsOK s (locN s "stable_logs", 24) ∧
      ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p)))
      (.store (.op .add [.var .local (ofString "stable_logs"), .const 8])
        (.var .local (ofString "nl")))
      (fun r t => r = none → StableLengthPost t ∧ locN t "logs" ≠ 0 ∧
        WordsOK t (locN t "stable_logs", 24) ∧ Allocated t (locN t "stable_logs", 24) ∧
        locN t "nl" ≤ locN t "stable_log_cap" ∧ StableCopySpatial t ∧
        WordAt t (locN t "stable_logs") ∧ ∃ n p w : BitVec 64,
          t.locals.lookup (ofString "nl") = some (.val (.word n)) ∧
          t.locals.lookup (ofString "lp") = some (.val (.word p)) ∧
          t.locals.lookup (ofString "stable_logs") = some (.val (.word w))) := by
  constructor
  intro F s hc hp hnt hr
  obtain ⟨hpost, hs⟩ := hoare_stable_length_joint.run s hc hp.1 hnt hr
  have hcap : locN s "nl" ≤ locN s "stable_log_cap" :=
    stableLengthPre_copy_capacity s hp.1.1 s.memory
  obtain ⟨hz, hh, ha, hcap', hw, hop⟩ := hoare_stable_length_setup_frame.run s hc
    ⟨hp.1.1, hp.2.1, hp.2.2.1, hcap, hp.2.2.2⟩ hnt hr
  exact ⟨hpost, hz, hh, ha, hcap', hs, hw, hop⟩

/-- The copy-ready length write also retains the coherent ownership witness. -/
theorem hoare_stable_length_owned_copy_ready :
    Hoare (fun s => (StableLengthPre s ∧ StableCopyOwnedFrame s ∧
      Disj (locN s "logs", 24)
        (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
      Disj (locN s "stable_logs", 24)
        (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
      Disj (memW s (locN s "logs"), 8 * memW s (locN s "logs" + 8))
        (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
      ∀ j, j < memW s (locN s "logs" + 8) →
        Disj (memW s (memW s (locN s "logs") + 8 * j), 40)
          (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap")) ∧
      locN s "logs" ≠ 0 ∧ WordsOK s (locN s "stable_logs", 24) ∧
      ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p)))
      (.store (.op .add [.var .local (ofString "stable_logs"), .const 8])
        (.var .local (ofString "nl")))
      (fun r t => r = none → (StableLengthPost t ∧ locN t "logs" ≠ 0 ∧
        WordsOK t (locN t "stable_logs", 24) ∧ Allocated t (locN t "stable_logs", 24) ∧
        locN t "nl" ≤ locN t "stable_log_cap" ∧ StableCopySpatial t ∧
        WordAt t (locN t "stable_logs") ∧ ∃ n p w : BitVec 64,
          t.locals.lookup (ofString "nl") = some (.val (.word n)) ∧
          t.locals.lookup (ofString "lp") = some (.val (.word p)) ∧
          t.locals.lookup (ofString "stable_logs") = some (.val (.word w))) ∧
        StableCopyOwnedFrame t) := by
  constructor
  intro F s hc hp hnt hr
  exact ⟨hoare_stable_length_copy_ready.run s hc hp hnt hr,
    hoare_stable_length_ownedFrame.run s hc ⟨hp.1.1, hp.1.2.1⟩ hnt hr⟩

/-- Reassemble the separated store contract from framed source cells and
preserved ownership after a memory update. -/
theorem stableCopyStorePre_memory {F : Type} (s : PanSemStateFiniteExact 64 F)
    (mem' : BitVec 64 → HolWordLab 64) (hp : StableCopyStorePre s)
    (hinv : StableCopyInv {s with memory := mem'})
    (hs : memW {s with memory := mem'} (locN s "logs") = memW s (locN s "logs"))
    (hn : memW {s with memory := mem'} (locN s "logs" + 8) =
      memW s (locN s "logs" + 8))
    (hd : memW {s with memory := mem'} (locN s "stable_logs") =
      memW s (locN s "stable_logs"))
    (ha : ∀ j, j < memW s (locN s "logs" + 8) →
      memW {s with memory := mem'} (memW s (locN s "logs") + 8 * j) =
        memW s (memW s (locN s "logs") + 8 * j))
    (hworld : ∀ S Nd, WorldTypedWith s S Nd →
      LogsLiveOwned s S Nd (locN s "logs") →
      WorldTypedWith {s with memory := mem'} S Nd ∧
      LogsLiveOwned {s with memory := mem'} S Nd (locN s "logs") ∧
      worldOwned {s with memory := mem'} S Nd = worldOwned s S Nd) :
    StableCopyStorePre {s with memory := mem'} := by
  obtain ⟨_, hi, ⟨w, p, q, hw, hl, hq, hptr⟩,
    S, Nd, hW, ho, hsep, hh, hdh, harr, he⟩ := hp
  obtain ⟨hW', ho', howned⟩ := hworld S Nd hW ho
  refine ⟨hinv, hi, ⟨w, p, q, hw, hl, hq, ?_⟩,
    S, Nd, hW', ho', ?_, ?_, ?_, ?_, ?_⟩
  · exact hptr.trans hd.symm
  · exact stable_copy_world_separation s mem' S Nd hd howned hsep
  · change Disj (locN s "logs", 24)
      (memW {s with memory := mem'} (locN s "stable_logs"), 8 * locN s "stable_log_cap")
    rw [hd]; exact hh
  · change Disj (locN s "stable_logs", 24)
      (memW {s with memory := mem'} (locN s "stable_logs"), 8 * locN s "stable_log_cap")
    rw [hd]; exact hdh
  · change Disj (memW {s with memory := mem'} (locN s "logs"),
      8 * memW {s with memory := mem'} (locN s "logs" + 8))
      (memW {s with memory := mem'} (locN s "stable_logs"), 8 * locN s "stable_log_cap")
    rw [hs, hn, hd]; exact harr
  · exact stable_copy_record_separation s mem' hs hn hd ha he

/-- The copy write preserves the already copied prefix as well as the
length postcondition, before the counter is advanced. -/
theorem stableCopyInv_after_store {F : Type} (s : PanSemStateFiniteExact 64 F)
    (mem' : BitVec 64 → HolWordLab 64) (hp : StableCopyInv s)
    (hpost : StableLengthPost {s with memory := mem'})
    (hi : locN s "i" < locN s "nl")
    (hwrite : memW {s with memory := mem'}
      (memW s (locN s "stable_logs") + 8 * locN s "i") =
      memW s (memW s (locN s "logs") + 8 * locN s "i"))
    (hm : ∀ a, a ≠ BitVec.ofNat 64
      (memW s (locN s "stable_logs") + 8 * locN s "i") → mem' a = s.memory a)
    (hsource : ∀ j, j < locN s "nl" →
      memW {s with memory := mem'} (memW s (locN s "logs") + 8 * j) =
        memW s (memW s (locN s "logs") + 8 * j))
    (hs : memW {s with memory := mem'} (locN s "logs") = memW s (locN s "logs"))
    (hd : memW {s with memory := mem'} (locN s "stable_logs") =
      memW s (locN s "stable_logs")) : StableCopyInv {s with memory := mem'} := by
  refine ⟨hpost, hp.2.1, ?_, hp.2.2.2.1, hp.2.2.2.2.1, ?_⟩
  · exact wordsOK_transfer hp.1.1.1.1.1 hpost.1.1.1.1 hp.2.2.1
  · intro j hj hjn
    change j < locN s "i" at hj
    exact stableCopyInv_store_prefix s mem' hp hi hwrite hm hsource hs hd j (by omega)

/-- Loop-head contract: operand shapes, bounded counter, and the separated
store precondition whenever the current index is active. -/
def StableCopyLoopInv : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => StableCopyInv s ∧
    (∃ i n : BitVec 64,
      s.locals.lookup (ofString "i") = some (.val (.word i)) ∧
      s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
    locN s "i" ≤ locN s "nl" ∧
    (locN s "i" < locN s "nl" → StableCopyStorePre s)

/-- An active separated store state supplies every loop-head premise;
positivity of the length recovers its word-shaped local. -/
theorem stableCopyStorePre_loopInv {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableCopyStorePre s) : StableCopyLoopInv s := by
  obtain ⟨w, p, q, hw, _⟩ := hp.2.2.1
  have hn : 0 < locN s "nl" := Nat.lt_of_le_of_lt (Nat.zero_le _) hp.2.1
  exact ⟨hp.1, ⟨w, BitVec.ofNat 64 (locN s "nl"), hw,
    stable_positive_local_word s "nl" hn⟩, Nat.le_of_lt hp.2.1, fun _ => hp⟩

/-- A completed copy needs no further separation premise at the loop head. -/
theorem stableCopyLoopInv_complete {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableCopyInv s)
    (hshape : ∃ i n : BitVec 64,
      s.locals.lookup (ofString "i") = some (.val (.word i)) ∧
      s.locals.lookup (ofString "nl") = some (.val (.word n)))
    (he : locN s "i" = locN s "nl") : StableCopyLoopInv s := by
  refine ⟨hp, hshape, Nat.le_of_eq he, ?_⟩
  intro hi
  omega

/-- Empty source lists enter the completed loop directly after zeroing the counter. -/
theorem stableCopyLoopInv_init_empty {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableLengthPost s) (hn : locN s "logs" ≠ 0)
    (hh : WordsOK s (locN s "stable_logs", 24))
    (ha : Allocated s (locN s "stable_logs", 24))
    (hcap : locN s "nl" ≤ locN s "stable_log_cap")
    (hz : s.locals.lookup (ofString "nl") = some (.val (.word 0))) :
    StableCopyLoopInv (setVarHOLFinite (ofString "i") (.val (.word 0)) s) := by
  apply stableCopyLoopInv_complete _ (stableCopyInv_init s hp hn hh ha hcap)
  · refine ⟨0, 0, ?_, ?_⟩ <;>
      simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hz]
  · simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hz]

/-- The concrete zero assignment establishes the empty-source loop invariant. -/
theorem hoare_stableCopy_init_empty :
    Hoare (fun s => StableLengthPost s ∧ locN s "logs" ≠ 0 ∧
      WordsOK s (locN s "stable_logs", 24) ∧
      Allocated s (locN s "stable_logs", 24) ∧
      locN s "nl" ≤ locN s "stable_log_cap" ∧
      s.locals.lookup (ofString "nl") = some (.val (.word 0)))
      (.assign .local (ofString "i") (.const 0))
      (fun r t => r = none → StableCopyLoopInv t) := by
  apply Hoare.assign
  · intro F s v hp hv _
    have hv' : v = .val (.word 0) := by simpa [evalAt, evalHOLExact] using hv.symm
    subst v
    exact stableCopyLoopInv_init_empty s hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1
      hp.2.2.2.2.1 hp.2.2.2.2.2
  · intro F s hp hr
    cases hr

/-- A separated active-store state already satisfies the full loop-head
contract; positivity supplies the length operand's word shape. -/
theorem stableCopyLoopInv_of_storePre {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableCopyStorePre s) : StableCopyLoopInv s := by
  obtain ⟨w, p, q, hw, hl, hq, hptr⟩ := hp.2.2.1
  have hn := stable_positive_local_word s "nl" (by have := hp.2.1; omega)
  exact ⟨hp.1, ⟨w, BitVec.ofNat 64 (locN s "nl"), hw, hn⟩,
    Nat.le_of_lt hp.2.1, fun _ => hp⟩

/-- Clock decrement preserves the separated store contract. -/
theorem stableCopyStorePre_decClock {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableCopyStorePre s) : StableCopyStorePre (decClockHOLFinite s) := by
  obtain ⟨hinv, hi, hshape, S, Nd, hW, ho, hworld, hh, hd, ha, he⟩ := hp
  refine ⟨stableCopyInv_with_locals s s.locals (s.clock - 1) (by intros; rfl) hinv,
    hi, hshape, S, Nd, ?_, ho, hworld, hh, hd, ha, he⟩
  exact (R13Shards.worldTypedWith_with_locals s s.locals (s.clock - 1) S Nd).mpr hW

/-- The loop-head contract survives the loop's clock decrement. -/
theorem stableCopyLoopInv_decClock {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableCopyLoopInv s) : StableCopyLoopInv (decClockHOLFinite s) := by
  refine ⟨stableCopyInv_with_locals s s.locals (s.clock - 1) (by intros; rfl) hp.1,
    hp.2.1, hp.2.2.1, ?_⟩
  intro hi
  exact stableCopyStorePre_decClock s (hp.2.2.2 hi)

theorem stableCopyLoopInv_rank {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableCopyLoopInv s) : locN s "nl" - locN s "i" ≤ 2 ^ 28 := by
  have hb := (stableLengthPost_length_bound s hp.1.1 hp.1.2.1).1
  omega

theorem stableCopyLoopInv_active {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableCopyLoopInv s)
    (ha : LoopActive (.cmp .less (.var .local (ofString "i"))
      (.var .local (ofString "nl"))) s) : StableCopyStorePre s := by
  obtain ⟨w, hw, hnz⟩ := ha
  obtain ⟨i, n, hi, hn⟩ := hp.2.1
  have hb := (stableLengthPost_length_bound s hp.1.1 hp.1.2.1).1
  exact hp.2.2.2 (stableCopyInv_guard s hp.1 i n w hi hn (by have := hp.2.2.1; omega) hw hnz)

theorem stableCopyLoopInv_done {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableCopyLoopInv s)
    (he : evalAt s (.cmp .less (.var .local (ofString "i"))
      (.var .local (ofString "nl"))) = some (.val (.word 0))) : PtxReceiptsDone s := by
  obtain ⟨i, n, hi, hn⟩ := hp.2.1
  have hb := (stableLengthPost_length_bound s hp.1.1 hp.1.2.1).1
  apply stableCopyInv_exit s hp.1
  exact stableCopyInv_guard_false s hp.1 i n hi hn (by have := hp.2.2.1; omega) he

/-- A false copy guard yields receipts together with stable-list ownership. -/
theorem stableCopyLoopInv_done_owned {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableCopyLoopInv s) (hf : StableCopyOwnedFrame s)
    (he : evalAt s (.cmp .less (.var .local (ofString "i"))
      (.var .local (ofString "nl"))) = some (.val (.word 0))) :
    PtxReceiptsDone s ∧ LogsWorldOwned s (locN s "stable_logs") := by
  obtain ⟨i, n, hi, hn⟩ := hp.2.1
  have hb := (stableLengthPost_length_bound s hp.1.1 hp.1.2.1).1
  apply stableCopyOwnedFrame_exit s hp.1 hf
  exact stableCopyInv_guard_false s hp.1 i n hi hn
    (by have := hp.2.2.1; omega) he

/-- The actual indexed copy store preserves the length postcondition. -/
theorem hoare_stableCopy_store_post :
    Hoare StableCopyStorePre
      (.store (.op .add [.var .local (ofString "stable_lp"),
        .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
      (fun r t => r = none → StableLengthPost t) := by
  refine R13Shards.Hoare.store_fall fun s x v mem' hp hx hv hst => ?_
  obtain ⟨hinv, hi, ⟨w, p, q, hw, hl, hq, hptr⟩,
    S, Nd, hW, ho, hworld, hh, hd, ha, he⟩ := hp
  have hx' := stable_copy_destination_address_eval s w q hinv hw hq hptr hi
  rw [hx] at hx'
  have hxe : x = BitVec.ofNat 64
      (memW s (locN s "stable_logs") + 8 * locN s "i") := by
    simpa using Option.some.inj hx'
  subst x
  obtain ⟨hdom, _, hm⟩ := stable_copy_store_semantics s mem' w p hinv hw hl hi v hv hst
  exact stableCopyInv_store_post s mem' hinv hi S Nd hW ho hworld hh hd ha he hdom hm

/-- The copy store establishes the extended prefix needed by the increment. -/
theorem hoare_stableCopy_store_prefix :
    Hoare StableCopyStorePre
      (.store (.op .add [.var .local (ofString "stable_lp"),
        .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
      (fun r t => r = none → ∀ j, j < locN t "i" + 1 → j < locN t "nl" →
        memW t (memW t (locN t "stable_logs") + 8 * j) =
          memW t (memW t (locN t "logs") + 8 * j)) := by
  refine R13Shards.Hoare.store_fall fun s x v mem' hp hx hv hst => ?_
  obtain ⟨hinv, hi, ⟨w, p, q, hw, hl, hq, hptr⟩,
    S, Nd, hW, ho, hworld, hh, hd, ha, he⟩ := hp
  have hx' := stable_copy_destination_address_eval s w q hinv hw hq hptr hi
  rw [hx] at hx'
  have hxe : x = BitVec.ofNat 64
      (memW s (locN s "stable_logs") + 8 * locN s "i") := by
    simpa using Option.some.inj hx'
  subst x
  obtain ⟨hdom, hwrite, hm⟩ := stable_copy_store_semantics s mem' w p hinv hw hl hi v hv hst
  have hlogs := hinv.1.2.1.resolve_left hinv.2.1
  have hs0 := (stableCopyInv_header_unhit s mem' hinv hi _ hlogs.2.1 hlogs.1.1 hh hm).1
  have hd0 := (stableCopyInv_header_unhit s mem' hinv hi _
    hinv.2.2.2.1 hinv.2.2.1.1 hd hm).1
  have ha' : Disj (locN s "lp", 8 * locN s "nl")
      (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") := by
    rw [hinv.1.2.2.2.2.1, hinv.1.2.2.2.1]; exact ha
  have harr := stableCopyInv_source_preserved s mem' hinv hi ha' hm
  rw [hinv.1.2.2.2.2.1] at harr
  intro j hj _
  exact stableCopyInv_store_prefix s mem' hinv hi hwrite hm harr hs0 hd0 j hj

/-- The concrete store retains the invariant at the old counter, allowing
the separation contract to be reconstructed before incrementing. -/
theorem hoare_stableCopy_store_inv :
    Hoare StableCopyStorePre
      (.store (.op .add [.var .local (ofString "stable_lp"),
        .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
      (fun r t => r = none → StableCopyInv t) := by
  refine R13Shards.Hoare.store_fall fun s x v mem' hp hx hv hst => ?_
  obtain ⟨hinv, hi, ⟨w, p, q, hw, hl, hq, hptr⟩,
    S, Nd, hW, ho, hworld, hh, hd, ha, he⟩ := hp
  have hx' := stable_copy_destination_address_eval s w q hinv hw hq hptr hi
  rw [hx] at hx'
  have hxe : x = BitVec.ofNat 64
      (memW s (locN s "stable_logs") + 8 * locN s "i") := by
    simpa using Option.some.inj hx'
  subst x
  obtain ⟨hdom, hwrite, hm⟩ := stable_copy_store_semantics s mem' w p hinv hw hl hi v hv hst
  have hpost := stableCopyInv_store_post s mem' hinv hi S Nd hW ho hworld hh hd ha he hdom hm
  have hlogs := hinv.1.2.1.resolve_left hinv.2.1
  have hs0 := (stableCopyInv_header_unhit s mem' hinv hi _ hlogs.2.1 hlogs.1.1 hh hm).1
  have hd0 := (stableCopyInv_header_unhit s mem' hinv hi _
    hinv.2.2.2.1 hinv.2.2.1.1 hd hm).1
  have ha' : Disj (locN s "lp", 8 * locN s "nl")
      (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") := by
    rw [hinv.1.2.2.2.2.1, hinv.1.2.2.2.1]; exact ha
  have harr := stableCopyInv_source_preserved s mem' hinv hi ha' hm
  rw [hinv.1.2.2.2.2.1] at harr
  exact stableCopyInv_after_store s mem' hinv hpost hi hwrite hm harr hs0 hd0

/-- A separated concrete copy store preserves the full store contract at
the old index, including its ownership witnesses. -/
theorem hoare_stableCopy_store_pre :
    Hoare StableCopyStorePre
      (.store (.op .add [.var .local (ofString "stable_lp"),
        .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
      (fun r t => r = none → StableCopyStorePre t) := by
  refine R13Shards.Hoare.store_fall fun s x v mem' hp hx hv hst => ?_
  obtain ⟨hinv, hi, ⟨w, p, q, hw, hl, hq, hptr⟩,
    S, Nd, hW, ho, hworld, hh, hd, ha, he⟩ := hp
  have hx' := stable_copy_destination_address_eval s w q hinv hw hq hptr hi
  rw [hx] at hx'
  have hxe : x = BitVec.ofNat 64
      (memW s (locN s "stable_logs") + 8 * locN s "i") := by
    simpa using Option.some.inj hx'
  subst x
  obtain ⟨hdom, hwrite, hm⟩ := stable_copy_store_semantics s mem' w p hinv hw hl hi v hv hst
  have hpost := stableCopyInv_store_post s mem' hinv hi S Nd hW ho hworld hh hd ha he hdom hm
  have hlogs := hinv.1.2.1.resolve_left hinv.2.1
  obtain ⟨hs0, hs8, _⟩ := stableCopyInv_header_unhit s mem' hinv hi _ hlogs.2.1 hlogs.1.1 hh hm
  have hd0 := (stableCopyInv_header_unhit s mem' hinv hi _
    hinv.2.2.2.1 hinv.2.2.1.1 hd hm).1
  have ha' : Disj (locN s "lp", 8 * locN s "nl")
      (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") := by
    rw [hinv.1.2.2.2.2.1, hinv.1.2.2.2.1]; exact ha
  have harr := stableCopyInv_source_preserved s mem' hinv hi ha' hm
  rw [hinv.1.2.2.2.2.1] at harr
  have hinv' := stableCopyInv_after_store s mem' hinv hpost hi hwrite hm harr hs0 hd0
  obtain ⟨hW', howned, _⟩ := stableCopyInv_world_preserved s mem' hinv hi S Nd hW hworld hdom hm
  have ho' := (stableCopyInv_logs_preserved s mem' hinv hi S Nd ho
    hpost.1.1.1.1 howned hh ha he hm).2
  refine ⟨hinv', hi, ⟨w, p, q, hw, hl, hq, hptr.trans hd0.symm⟩,
    S, Nd, hW', ho', ?_, ?_, ?_, ?_, ?_⟩
  · exact stable_copy_world_separation s mem' S Nd hd0 howned hworld
  · change Disj (locN s "logs", 24)
      (memW {s with memory := mem'} (locN s "stable_logs"), 8 * locN s "stable_log_cap")
    rw [hd0]; exact hh
  · change Disj (locN s "stable_logs", 24)
      (memW {s with memory := mem'} (locN s "stable_logs"), 8 * locN s "stable_log_cap")
    rw [hd0]; exact hd
  · change Disj (memW {s with memory := mem'} (locN s "logs"),
      8 * memW {s with memory := mem'} (locN s "logs" + 8))
      (memW {s with memory := mem'} (locN s "stable_logs"), 8 * locN s "stable_log_cap")
    rw [hs0, hs8, hd0]; exact ha
  · apply stable_copy_record_separation s mem' hs0 hs8 hd0 _ he
    intro j hj
    apply harr j
    rwa [hinv.1.2.2.2.1]

/-- The copy store retains the typed length operand for the increment rule. -/
theorem hoare_stableCopy_store_length_shape :
    Hoare (fun s => StableCopyStorePre s ∧
      ∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n)))
      (.store (.op .add [.var .local (ofString "stable_lp"),
        .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
      (fun r t => r = none → ∃ n : BitVec 64,
        t.locals.lookup (ofString "nl") = some (.val (.word n))) := by
  refine R13Shards.Hoare.store_fall fun s x v mem' hp hx hv hst => ?_
  exact hp.2

/-- The concrete store retains the typed length operand required by the
full-invariant increment rule. -/
theorem hoare_stableCopy_store_length_word :
    Hoare (fun s => ∃ n : BitVec 64,
      s.locals.lookup (ofString "nl") = some (.val (.word n)))
      (.store (.op .add [.var .local (ofString "stable_lp"),
        .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
      (fun r t => r = none → ∃ n : BitVec 64,
        t.locals.lookup (ofString "nl") = some (.val (.word n))) := by
  exact R13Shards.Hoare.store_fall (fun _ _ _ _ hp _ _ _ => hp)

/-- The actual copy-loop counter increment agrees with natural-number
successor throughout the bounded source list. -/
theorem stable_copy_increment_nat {F : Type} (s : PanSemStateFiniteExact 64 F)
    (w : BitVec 64) (v : ValueHOL 64)
    (hw : s.locals.lookup (ofString "i") = some (.val (.word w)))
    (hi : w.toNat < locN s "nl") (hn : locN s "nl" < 2 ^ 28)
    (he : evalAt s (.op .add [.var .local (ofString "i"), .const 1]) = some v) :
    locN (setVarHOLFinite (ofString "i") v s) "i" = w.toNat + 1 := by
  have hv : v = .val (.word (w + 1)) := by
    simpa [evalAt, evalHOLExact, evalListHOLExact, hw, valueIsWord,
      valueWord, wordOpHOL, wordOp] using he.symm
  subst v
  have hb : w.toNat + 1 < 2 ^ 64 := by omega
  simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
    BitVec.toNat_add]
  exact hb

/-- An active copy iteration keeps the incremented index in the unsigned
range where the signed loop guard agrees with natural comparison. -/
theorem stable_copy_increment_index_bound {F : Type} (s : PanSemStateFiniteExact 64 F)
    (w : BitVec 64) (v : ValueHOL 64)
    (hw : s.locals.lookup (ofString "i") = some (.val (.word w)))
    (hi : w.toNat < locN s "nl") (hn : locN s "nl" < 2 ^ 28)
    (he : evalAt s (.op .add [.var .local (ofString "i"), .const 1]) = some v) :
    locN (setVarHOLFinite (ofString "i") v s) "i" ≤ locN s "nl" ∧
    locN (setVarHOLFinite (ofString "i") v s) "i" < 2 ^ 63 := by
  rw [stable_copy_increment_nat s w v hw hi hn he]
  constructor <;> omega

/-- The remaining-copy count strictly decreases under the actual increment,
providing a natural-number termination measure for the copy loop. -/
theorem stableCopyInv_increment_decreases {F : Type} (s : PanSemStateFiniteExact 64 F)
    (w : BitVec 64) (v : ValueHOL 64) (hp : StableCopyInv s)
    (hw : s.locals.lookup (ofString "i") = some (.val (.word w)))
    (hi : locN s "i" < locN s "nl")
    (he : evalAt s (.op .add [.var .local (ofString "i"), .const 1]) = some v) :
    locN (setVarHOLFinite (ofString "i") v s) "nl" -
        locN (setVarHOLFinite (ofString "i") v s) "i" <
      locN s "nl" - locN s "i" := by
  have hwi : locN s "i" = w.toNat := by simp [locN, hw]
  have hinc := stable_copy_increment_nat s w v hw (by rw [← hwi]; exact hi)
    (stableLengthPost_length_bound s hp.1 hp.2.1).1 he
  have hnl : locN (setVarHOLFinite (ofString "i") v s) "nl" = locN s "nl" := by
    simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "i" ≠ ofString "nl" from by decide]
  rw [hnl, hinc]
  omega

/-- The increment retains a word-shaped counter for the next iteration. -/
theorem stable_copy_increment_word {F : Type} (s : PanSemStateFiniteExact 64 F)
    (w : BitVec 64) (v : ValueHOL 64)
    (hw : s.locals.lookup (ofString "i") = some (.val (.word w)))
    (he : evalAt s (.op .add [.var .local (ofString "i"), .const 1]) = some v) :
    (setVarHOLFinite (ofString "i") v s).locals.lookup (ofString "i") =
      some (.val (.word (w + 1))) := by
  have hv : v = .val (.word (w + 1)) := by
    simpa [evalAt, evalHOLExact, evalListHOLExact, hw, valueIsWord,
      valueWord, wordOpHOL, wordOp] using he.symm
  subst v
  simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]

/-- Incrementing the counter preserves the typed source, destination, and
length operands needed by the next loop iteration. -/
theorem stable_copy_increment_operands {F : Type} (s : PanSemStateFiniteExact 64 F)
    (w p q n : BitVec 64) (v : ValueHOL 64)
    (hw : s.locals.lookup (ofString "i") = some (.val (.word w)))
    (hp : s.locals.lookup (ofString "lp") = some (.val (.word p)))
    (hq : s.locals.lookup (ofString "stable_lp") = some (.val (.word q)))
    (hn : s.locals.lookup (ofString "nl") = some (.val (.word n)))
    (he : evalAt s (.op .add [.var .local (ofString "i"), .const 1]) = some v) :
    let t := setVarHOLFinite (ofString "i") v s
    t.locals.lookup (ofString "i") = some (.val (.word (w + 1))) ∧
    t.locals.lookup (ofString "lp") = some (.val (.word p)) ∧
    t.locals.lookup (ofString "stable_lp") = some (.val (.word q)) ∧
    t.locals.lookup (ofString "nl") = some (.val (.word n)) := by
  refine ⟨stable_copy_increment_word s w v hw he, ?_⟩
  simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE] using ⟨hp, hq, hn⟩

/-- Updating only the counter retains all store separation and operand facts
whenever the new counter remains active. -/
theorem stableCopyStorePre_counter {F : Type} (s : PanSemStateFiniteExact 64 F)
    (v : ValueHOL 64) (w : BitVec 64) (hp : StableCopyStorePre s)
    (hv : v = .val (.word w))
    (hinv : StableCopyInv (setVarHOLFinite (ofString "i") v s))
    (hi : locN (setVarHOLFinite (ofString "i") v s) "i" < locN s "nl") :
    StableCopyStorePre (setVarHOLFinite (ofString "i") v s) := by
  subst v
  obtain ⟨_, _, ⟨iw, p, q, _, hl, hq, hptr⟩,
    S, Nd, hW, ho, hworld, hh, hd, ha, he⟩ := hp
  have hW' : WorldTypedWith (setVarHOLFinite (ofString "i") (.val (.word w)) s) S Nd :=
    (R13Shards.worldTypedWith_with_locals s _ s.clock S Nd).mpr hW
  have hn0 : ofString "i" ≠ ofString "nl" := by decide
  have hl0 : ofString "i" ≠ ofString "lp" := by decide
  have hq0 : ofString "i" ≠ ofString "stable_lp" := by decide
  have hs0 : ofString "i" ≠ ofString "stable_logs" := by decide
  have hc0 : ofString "i" ≠ ofString "stable_log_cap" := by decide
  have hg0 : ofString "i" ≠ ofString "logs" := by decide
  refine ⟨hinv, ?_, ⟨w, p, q, ?_, ?_, ?_, ?_⟩,
    S, Nd, hW', ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [locN, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      if_pos rfl, if_neg hn0, if_neg hl0, if_neg hq0, if_neg hs0, if_neg hc0,
      if_neg hg0] at *
  all_goals first | assumption | rfl

/-- The increment restores the full loop-head contract from a separated
store state and the already established prefix invariant. -/
theorem stableCopyLoopInv_counter {F : Type} (s : PanSemStateFiniteExact 64 F)
    (w n : BitVec 64) (v : ValueHOL 64) (hp : StableCopyStorePre s)
    (hw : s.locals.lookup (ofString "i") = some (.val (.word w)))
    (hn : s.locals.lookup (ofString "nl") = some (.val (.word n)))
    (he : evalAt s (.op .add [.var .local (ofString "i"), .const 1]) = some v)
    (hinv : StableCopyInv (setVarHOLFinite (ofString "i") v s)) :
    StableCopyLoopInv (setVarHOLFinite (ofString "i") v s) := by
  have hv : v = .val (.word (w + 1)) := by
    simpa [evalAt, evalHOLExact, evalListHOLExact, hw, valueIsWord,
      valueWord, wordOpHOL, wordOp] using he.symm
  have hnl : (setVarHOLFinite (ofString "i") v s).locals.lookup (ofString "nl") =
      some (.val (.word n)) := by
    simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "i" ≠ ofString "nl" by decide] using hn
  have hloc : locN (setVarHOLFinite (ofString "i") v s) "nl" = locN s "nl" := by
    simp [locN, hnl, hn]
  have hi : w.toNat < locN s "nl" := by
    simpa [locN, hw] using hp.2.1
  have hb := (stable_copy_increment_index_bound s w v hw hi
    (stableLengthPost_length_bound s hp.1.1 hp.1.2.1).1 he).1
  refine ⟨hinv, ⟨w + 1, n, stable_copy_increment_word s w v hw he, hnl⟩, ?_, ?_⟩
  · rwa [hloc]
  · intro hactive
    apply stableCopyStorePre_counter s v (w + 1) hp hv hinv
    rwa [hloc] at hactive

/-- The zero-counter state is a full loop head once allocation and framing
have supplied its active-store contract. -/
theorem stableCopyLoopInv_zero {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableCopyInv s) (n : BitVec 64)
    (hi : s.locals.lookup (ofString "i") = some (.val (.word 0)))
    (hn : s.locals.lookup (ofString "nl") = some (.val (.word n)))
    (hstore : 0 < locN s "nl" → StableCopyStorePre s) :
    StableCopyLoopInv s := by
  have hz : locN s "i" = 0 := by simp [locN, hi]
  refine ⟨hp, ⟨0, n, hi, hn⟩, ?_, ?_⟩
  · rw [hz]; exact Nat.zero_le _
  · simpa only [hz] using hstore

/-- Combine initialized operands with the spatial and prefix contracts to
obtain the full loop head, including the empty-source case. -/
theorem stableCopyLoopInv_of_spatial_zero {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableCopyInv s) (hs : StableCopySpatial s) (n p q : BitVec 64)
    (hi : s.locals.lookup (ofString "i") = some (.val (.word 0)))
    (hn : s.locals.lookup (ofString "nl") = some (.val (.word n)))
    (hl : s.locals.lookup (ofString "lp") = some (.val (.word p)))
    (hq : s.locals.lookup (ofString "stable_lp") = some (.val (.word q)))
    (hd : q.toNat = memW s (locN s "stable_logs")) : StableCopyLoopInv s := by
  apply stableCopyLoopInv_zero s hp n hi hn
  intro hpos
  refine ⟨hp, ?_, ⟨0, p, q, hi, hl, hq, hd⟩, hs⟩
  simpa [locN, hi] using hpos

/-- Counter initialization combines the retained spatial facts and typed
operands into the full copy-loop invariant. -/
theorem stableCopyLoopInv_init_spatial {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableLengthPost s) (hz : locN s "logs" ≠ 0)
    (hh : WordsOK s (locN s "stable_logs", 24))
    (ha : Allocated s (locN s "stable_logs", 24))
    (hc : locN s "nl" ≤ locN s "stable_log_cap")
    (hs : StableCopySpatial s) (n p q : BitVec 64)
    (hn : s.locals.lookup (ofString "nl") = some (.val (.word n)))
    (hl : s.locals.lookup (ofString "lp") = some (.val (.word p)))
    (hq : s.locals.lookup (ofString "stable_lp") = some (.val (.word q)))
    (hd : q.toNat = memW s (locN s "stable_logs")) :
    StableCopyLoopInv (setVarHOLFinite (ofString "i") (.val (.word 0)) s) := by
  have hsp : StableCopySpatial (setVarHOLFinite (ofString "i") (.val (.word 0)) s) := by
    apply stableCopySpatial_with_locals s _ s.clock (hp := hs) <;>
      simp [HolFiniteMapExact.update, FUPDATE, ofString]
  apply stableCopyLoopInv_of_spatial_zero _ (stableCopyInv_init s hp hz hh ha hc) hsp n p q
  · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  · simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, ofString] using hn
  · simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, ofString] using hl
  · simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, ofString] using hq
  · simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, locN, memW, ofString] using hd

/-- Loading the backing pointer and then zeroing the counter establishes the
loop invariant directly from the post-length state. -/
theorem stableCopyLoopInv_backing_init {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : StableLengthPost s) (hz : locN s "logs" ≠ 0)
    (hh : WordsOK s (locN s "stable_logs", 24))
    (ha : Allocated s (locN s "stable_logs", 24))
    (hc : locN s "nl" ≤ locN s "stable_log_cap")
    (hs : StableCopySpatial s) (n p w : BitVec 64) (v : ValueHOL 64)
    (hn : s.locals.lookup (ofString "nl") = some (.val (.word n)))
    (hl : s.locals.lookup (ofString "lp") = some (.val (.word p)))
    (hw : s.locals.lookup (ofString "stable_logs") = some (.val (.word w)))
    (hword : WordAt s (locN s "stable_logs"))
    (he : evalAt s (.load .one (.var .local (ofString "stable_logs"))) = some v) :
    StableCopyLoopInv (setVarHOLFinite (ofString "i") (.val (.word 0))
      (setVarHOLFinite (ofString "stable_lp") v s)) := by
  obtain ⟨q, hq, hd⟩ := stable_backing_load_local s w v hw hword he
  apply stableCopyLoopInv_init_spatial _ (stableLengthPost_set_backing s v hp)
    (n := n) (p := p) (q := q)
  · simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, locN, ofString] using hz
  · simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, locN, WordsOK, WordAt, ofString] using hh
  · simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, locN, Allocated, globN, ofString] using ha
  · simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, locN, ofString] using hc
  · exact stableCopySpatial_setVar s _ v (by decide) (by decide) (by decide) hs
  · simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, ofString] using hn
  · simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, ofString] using hl
  · exact hq
  · simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, locN, memW, ofString] using hd

/-- Backing assignment establishes the precondition for zero-counter entry. -/
theorem hoare_stableCopy_backing_entry :
    Hoare (fun s => StableLengthPost s ∧ locN s "logs" ≠ 0 ∧
      WordsOK s (locN s "stable_logs", 24) ∧ Allocated s (locN s "stable_logs", 24) ∧
      locN s "nl" ≤ locN s "stable_log_cap" ∧ StableCopySpatial s ∧
      WordAt s (locN s "stable_logs") ∧ ∃ n p w : BitVec 64,
        s.locals.lookup (ofString "nl") = some (.val (.word n)) ∧
        s.locals.lookup (ofString "lp") = some (.val (.word p)) ∧
        s.locals.lookup (ofString "stable_logs") = some (.val (.word w)))
      (.assign .local (ofString "stable_lp")
        (.load .one (.var .local (ofString "stable_logs"))))
      (fun r t => r = none →
        StableCopyLoopInv (setVarHOLFinite (ofString "i") (.val (.word 0)) t)) := by
  apply Hoare.assign
  · intro F s v hp he _
    obtain ⟨hp, hz, hh, ha, hc, hs, hword, n, p, w, hn, hl, hw⟩ := hp
    exact stableCopyLoopInv_backing_init s hp hz hh ha hc hs n p w v hn hl hw hword he
  · intro F s hp hr
    cases hr

/-- Hoare rule for the concrete backing-load and zero-counter setup sequence. -/
theorem hoare_stableCopy_backing_init :
    Hoare (fun s => StableLengthPost s ∧ locN s "logs" ≠ 0 ∧
      WordsOK s (locN s "stable_logs", 24) ∧ Allocated s (locN s "stable_logs", 24) ∧
      locN s "nl" ≤ locN s "stable_log_cap" ∧ StableCopySpatial s ∧
      WordAt s (locN s "stable_logs") ∧ ∃ n p w : BitVec 64,
        s.locals.lookup (ofString "nl") = some (.val (.word n)) ∧
        s.locals.lookup (ofString "lp") = some (.val (.word p)) ∧
        s.locals.lookup (ofString "stable_logs") = some (.val (.word w)))
      (.seq (.assign .local (ofString "stable_lp")
        (.load .one (.var .local (ofString "stable_logs"))))
        (.assign .local (ofString "i") (.const 0)))
      (fun r t => r = none → StableCopyLoopInv t) := by
  apply Hoare.seq_fall (R := fun s =>
    StableCopyLoopInv (setVarHOLFinite (ofString "i") (.val (.word 0)) s))
  · apply Hoare.assign
    · intro F s v hp hv _
      obtain ⟨hp, hz, hh, ha, hc, hs, hword, n, p, w, hn, hl, hw⟩ := hp
      exact stableCopyLoopInv_backing_init s hp hz hh ha hc hs n p w v hn hl hw hword hv
    · intro F s hp hr
      cases hr
  · apply Hoare.assign
    · intro F s v hp hv _
      have hv' : v = .val (.word 0) := by simpa [evalAt, evalHOLExact] using hv.symm
      subst v
      exact hp
    · intro F s hp hr
      cases hr

/-- Backing-pointer and counter setup jointly preserve coherent ownership. -/
theorem hoare_stableCopy_backing_init_owned :
    Hoare (fun s => (StableLengthPost s ∧ locN s "logs" ≠ 0 ∧
      WordsOK s (locN s "stable_logs", 24) ∧ Allocated s (locN s "stable_logs", 24) ∧
      locN s "nl" ≤ locN s "stable_log_cap" ∧ StableCopySpatial s ∧
      WordAt s (locN s "stable_logs") ∧ ∃ n p w : BitVec 64,
        s.locals.lookup (ofString "nl") = some (.val (.word n)) ∧
        s.locals.lookup (ofString "lp") = some (.val (.word p)) ∧
        s.locals.lookup (ofString "stable_logs") = some (.val (.word w))) ∧
      StableCopyOwnedFrame s)
      (.seq (.assign .local (ofString "stable_lp")
        (.load .one (.var .local (ofString "stable_logs"))))
        (.assign .local (ofString "i") (.const 0)))
      (fun r t => r = none → StableCopyLoopInv t ∧ StableCopyOwnedFrame t) := by
  have hf := Hoare.seq_fall
    (hoare_stableCopyOwnedFrame_assign (ofString "stable_lp")
      (.load .one (.var .local (ofString "stable_logs")))
      (by decide) (by decide) (by decide))
    (hoare_stableCopyOwnedFrame_assign (ofString "i") (.const 0)
      (by decide) (by decide) (by decide))
  exact ⟨fun s hc hp hnt hr =>
    ⟨hoare_stableCopy_backing_init.run s hc hp.1 hnt hr,
      hf.run s hc hp.2 hnt hr⟩⟩

/-- Zeroing the counter realizes the loop-entry weakest precondition. -/
theorem hoare_stableCopy_zero_entry :
    Hoare (fun s => StableCopyLoopInv
      (setVarHOLFinite (ofString "i") (.val (.word 0)) s))
      (.assign .local (ofString "i") (.const 0))
      (fun r t => r = none → StableCopyLoopInv t) := by
  apply Hoare.assign
  · intro F s v hp hv _
    have hv' : v = .val (.word 0) := by simpa [evalAt, evalHOLExact] using hv.symm
    subst v
    exact hp
  · intro F s hp hr
    cases hr

/-- Concrete counter initialization from the post-length spatial contract. -/
theorem hoare_stableCopy_init_spatial :
    Hoare (fun s => StableLengthPost s ∧ locN s "logs" ≠ 0 ∧
      WordsOK s (locN s "stable_logs", 24) ∧ Allocated s (locN s "stable_logs", 24) ∧
      locN s "nl" ≤ locN s "stable_log_cap" ∧ StableCopySpatial s ∧
      ∃ n p q : BitVec 64,
        s.locals.lookup (ofString "nl") = some (.val (.word n)) ∧
        s.locals.lookup (ofString "lp") = some (.val (.word p)) ∧
        s.locals.lookup (ofString "stable_lp") = some (.val (.word q)) ∧
        q.toNat = memW s (locN s "stable_logs"))
      (.assign .local (ofString "i") (.const 0))
      (fun r t => r = none → StableCopyLoopInv t) := by
  apply Hoare.assign
  · intro F s v hp hv _
    have hv' : v = .val (.word 0) := by simpa [evalAt, evalHOLExact] using hv.symm
    subst v
    obtain ⟨hpost, hz, hh, ha, hc, hs, n, p, q, hn, hl, hq, hd⟩ := hp
    exact stableCopyLoopInv_init_spatial s hpost hz hh ha hc hs n p q hn hl hq hd
  · intro F s hp hr
    cases hr

/-- Assigning zero to the counter establishes the full loop contract when its
post-assignment allocation and separation obligations have been supplied. -/
theorem hoare_stableCopy_init_loop :
    Hoare (fun s =>
      StableCopyInv (setVarHOLFinite (ofString "i") (.val (.word 0)) s) ∧
      (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
      (0 < locN s "nl" →
        StableCopyStorePre (setVarHOLFinite (ofString "i") (.val (.word 0)) s)))
      (.assign .local (ofString "i") (.const 0))
      (fun r t => r = none → StableCopyLoopInv t) := by
  apply Hoare.assign
  · intro F s v hp hv _
    have hv' : v = .val (.word 0) := by simpa [evalAt, evalHOLExact] using hv.symm
    subst v
    obtain ⟨n, hn⟩ := hp.2.1
    have hnl : (setVarHOLFinite (ofString "i") (.val (.word 0)) s).locals.lookup
        (ofString "nl") = some (.val (.word n)) := by
      simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
        show ofString "i" ≠ ofString "nl" by decide] using hn
    apply stableCopyLoopInv_zero _ hp.1 n
    · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
    · exact hnl
    · simpa only [locN, hnl, hn] using hp.2.2
  · intro F s hp hr
    cases hr

/-- Hoare composition interface for the increment with full loop-head
preservation, including the separated contract for the next active index. -/
theorem hoare_stableCopy_increment_loop :
    Hoare (fun s => StableCopyStorePre s ∧
      (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
      ∀ v, evalAt s (.op .add [.var .local (ofString "i"), .const 1]) = some v →
        StableCopyInv (setVarHOLFinite (ofString "i") v s))
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))
      (fun r t => r = none → StableCopyLoopInv t) := by
  apply Hoare.assign
  · intro F s v hp hv _
    obtain ⟨n, hn⟩ := hp.2.1
    obtain ⟨w, p, q, hw, _⟩ := hp.1.2.2.1
    exact stableCopyLoopInv_counter s w n v hp.1 hw hn hv (hp.2.2 v hv)
  · intro F s hp hr
    cases hr

/-- Once the store has extended the prefix, the actual counter assignment
re-establishes the loop invariant. -/
theorem stableCopyInv_increment {F : Type} (s : PanSemStateFiniteExact 64 F)
    (w : BitVec 64) (v : ValueHOL 64)
    (hp : StableLengthPost s) (hn : locN s "logs" ≠ 0)
    (hh : WordsOK s (locN s "stable_logs", 24))
    (ha : Allocated s (locN s "stable_logs", 24))
    (hcap : locN s "nl" ≤ locN s "stable_log_cap")
    (hw : s.locals.lookup (ofString "i") = some (.val (.word w)))
    (hi : w.toNat < locN s "nl")
    (hprefix : ∀ j, j < w.toNat + 1 → j < locN s "nl" →
      memW s (memW s (locN s "stable_logs") + 8 * j) =
        memW s (memW s (locN s "logs") + 8 * j))
    (he : evalAt s (.op .add [.var .local (ofString "i"), .const 1]) = some v) :
    StableCopyInv (setVarHOLFinite (ofString "i") v s) := by
  have hpost : StableLengthPost (setVarHOLFinite (ofString "i") v s) :=
    LocalsOnly.setVar localsOnly_stableLengthPost (by decide) v s hp
  have hinc := stable_copy_increment_nat s w v hw hi
    (stableLengthPost_length_bound s hp hn).1 he
  have hloc : ∀ name ∈ (["logs", "stable_logs", "nl", "stable_log_cap"] : List String),
      locN (setVarHOLFinite (ofString "i") v s) name = locN s name := by
    intro name hname
    have hne : ofString "i" ≠ ofString name := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hname
      rcases hname with rfl | rfl | rfl | rfl <;> decide
    simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne]
  refine ⟨hpost, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hloc "logs" (by simp)]; exact hn
  · rw [hloc "stable_logs" (by simp)]; exact hh
  · rw [hloc "stable_logs" (by simp)]; exact ha
  · rw [hloc "nl" (by simp), hloc "stable_log_cap" (by simp)]; exact hcap
  · intro j hj hjn
    rw [hinc] at hj
    rw [hloc "nl" (by simp)] at hjn
    rw [hloc "stable_logs" (by simp), hloc "logs" (by simp)]
    exact hprefix j hj hjn

/-- Hoare rule for the actual increment once the copy store has extended
the prefix through the current index. -/
theorem hoare_stableCopy_increment :
    Hoare (fun s => StableLengthPost s ∧ locN s "logs" ≠ 0 ∧
      WordsOK s (locN s "stable_logs", 24) ∧ Allocated s (locN s "stable_logs", 24) ∧
      locN s "nl" ≤ locN s "stable_log_cap" ∧
      (∃ w : BitVec 64, s.locals.lookup (ofString "i") = some (.val (.word w))) ∧
      locN s "i" < locN s "nl" ∧
      ∀ j, j < locN s "i" + 1 → j < locN s "nl" →
        memW s (memW s (locN s "stable_logs") + 8 * j) =
          memW s (memW s (locN s "logs") + 8 * j))
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))
      (fun r t => r = none → StableCopyInv t) := by
  apply Hoare.assign
  · intro F s v hp hv _
    obtain ⟨hpost, hn, hh, ha, hc, ⟨w, hw⟩, hi, hprefix⟩ := hp
    have hwi : locN s "i" = w.toNat := by simp [locN, hw]
    apply stableCopyInv_increment s w v hpost hn hh ha hc hw
      (by rw [← hwi]; exact hi) ?_ hv
    intro j hj hjn
    exact hprefix j (by rw [hwi]; exact hj) hjn
  · intro F s hp hr
    exact absurd hr (by simp)

/-- Compose the semantic copy write with the actual counter assignment. -/
theorem stableCopyInv_store_increment {F : Type} (s : PanSemStateFiniteExact 64 F)
    (mem' : BitVec 64 → HolWordLab 64) (w : BitVec 64) (v : ValueHOL 64)
    (hp : StableCopyInv s) (hi : locN s "i" < locN s "nl")
    (hpost : StableLengthPost {s with memory := mem'})
    (hw : s.locals.lookup (ofString "i") = some (.val (.word w)))
    (hwrite : memW {s with memory := mem'}
      (memW s (locN s "stable_logs") + 8 * locN s "i") =
      memW s (memW s (locN s "logs") + 8 * locN s "i"))
    (hm : ∀ a, a ≠ BitVec.ofNat 64
      (memW s (locN s "stable_logs") + 8 * locN s "i") → mem' a = s.memory a)
    (hsource : ∀ j, j < locN s "nl" →
      memW {s with memory := mem'} (memW s (locN s "logs") + 8 * j) =
        memW s (memW s (locN s "logs") + 8 * j))
    (hsrc : memW {s with memory := mem'} (locN s "logs") = memW s (locN s "logs"))
    (hdst : memW {s with memory := mem'} (locN s "stable_logs") =
      memW s (locN s "stable_logs"))
    (he : evalAt {s with memory := mem'}
      (.op .add [.var .local (ofString "i"), .const 1]) = some v) :
    StableCopyInv (setVarHOLFinite (ofString "i") v {s with memory := mem'}) := by
  have hiw : locN s "i" = w.toNat := by simp [locN, hw]
  apply stableCopyInv_increment {s with memory := mem'} w v hpost hp.2.1
    (wordsOK_transfer hp.1.1.1.1.1 hpost.1.1.1.1 hp.2.2.1)
    hp.2.2.2.1 hp.2.2.2.2.1 hw (by change w.toNat < locN s "nl"; rw [← hiw]; exact hi) ?_ he
  intro j hj _
  exact stableCopyInv_store_prefix s mem' hp hi hwrite hm hsource hsrc hdst j
    (by simpa only [hiw] using hj)

/-- Assemble the source and header frame obligations for a separated store
before invoking the counter-increment invariant proof. -/
theorem stableCopyInv_separated_store_increment {F : Type}
    (s : PanSemStateFiniteExact 64 F) (mem' : BitVec 64 → HolWordLab 64)
    (w : BitVec 64) (v : ValueHOL 64) (hp : StableCopyInv s)
    (hi : locN s "i" < locN s "nl")
    (hpost : StableLengthPost {s with memory := mem'})
    (hw : s.locals.lookup (ofString "i") = some (.val (.word w)))
    (hwrite : memW {s with memory := mem'}
      (memW s (locN s "stable_logs") + 8 * locN s "i") =
      memW s (memW s (locN s "logs") + 8 * locN s "i"))
    (hm : ∀ a, a ≠ BitVec.ofNat 64
      (memW s (locN s "stable_logs") + 8 * locN s "i") → mem' a = s.memory a)
    (hs : Disj (locN s "logs", 24)
      (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap"))
    (hd : Disj (locN s "stable_logs", 24)
      (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap"))
    (ha : Disj (locN s "lp", 8 * locN s "nl")
      (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap"))
    (he : evalAt {s with memory := mem'}
      (.op .add [.var .local (ofString "i"), .const 1]) = some v) :
    StableCopyInv (setVarHOLFinite (ofString "i") v {s with memory := mem'}) := by
  have hl := hp.1.2.1.resolve_left hp.2.1
  have hsrc := (stableCopyInv_header_unhit s mem' hp hi _ hl.2.1 hl.1.1 hs hm).1
  have hdst := (stableCopyInv_header_unhit s mem' hp hi _
    hp.2.2.2.1 hp.2.2.1.1 hd hm).1
  have harr := stableCopyInv_source_preserved s mem' hp hi ha hm
  rw [hp.1.2.2.2.2.1] at harr
  exact stableCopyInv_store_increment s mem' w v hp hi hpost hw hwrite hm harr hsrc hdst he

/-- The semantic store establishes the precondition of the actual increment. -/
theorem hoare_stableCopy_store_for_increment :
    Hoare StableCopyStorePre
      (.store (.op .add [.var .local (ofString "stable_lp"),
        .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
      (fun r t => r = none → ∀ v,
        evalAt t (.op .add [.var .local (ofString "i"), .const 1]) = some v →
        StableCopyInv (setVarHOLFinite (ofString "i") v t)) := by
  refine R13Shards.Hoare.store_fall fun s x v mem' hp hx hv hst => ?_
  obtain ⟨hinv, hi, ⟨w, p, q, hw, hl, hq, hptr⟩,
    S, Nd, hW, ho, hworld, hh, hd, ha, he⟩ := hp
  have hx' := stable_copy_destination_address_eval s w q hinv hw hq hptr hi
  rw [hx] at hx'
  have hxe : x = BitVec.ofNat 64
      (memW s (locN s "stable_logs") + 8 * locN s "i") := by
    simpa using Option.some.inj hx'
  subst x
  obtain ⟨hdom, hwrite, hm⟩ := stable_copy_store_semantics s mem' w p hinv hw hl hi v hv hst
  have hpost := stableCopyInv_store_post s mem' hinv hi S Nd hW ho hworld hh hd ha he hdom hm
  have ha' : Disj (locN s "lp", 8 * locN s "nl")
      (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") := by
    rw [hinv.1.2.2.2.2.1, hinv.1.2.2.2.1]
    exact ha
  intro value hvalue
  exact stableCopyInv_separated_store_increment s mem' w value hinv hi hpost hw
    hwrite hm hh hd ha' hvalue

/-- Combine store framing and increment preservation into the full loop-head
contract for the concrete body. -/
theorem hoare_stableCopy_body_loop :
    Hoare (fun s => StableCopyStorePre s ∧
      ∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n)))
      (.seq (.store (.op .add [.var .local (ofString "stable_lp"),
        .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))
      (fun r t => r = none → StableCopyLoopInv t) := by
  apply Hoare.seq_fall (h2 := hoare_stableCopy_increment_loop)
  refine ⟨fun s hc hp hnt hr => ?_⟩
  exact ⟨hoare_stableCopy_store_pre.run s hc hp.1 hnt hr,
    hoare_stableCopy_store_length_word.run s hc hp.2 hnt hr,
    hoare_stableCopy_store_for_increment.run s hc hp.1 hnt hr⟩

/-- The indexed copy followed by its counter increment preserves ownership. -/
theorem hoare_stableCopy_body_ownedFrame :
    Hoare (fun s => StableCopyStorePre s ∧ StableCopyOwnedFrame s)
      (.seq (.store (.op .add [.var .local (ofString "stable_lp"),
        .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))
      (fun r t => r = none → StableCopyOwnedFrame t) := by
  exact Hoare.seq_fall hoare_stableCopy_store_ownedFrame
    (hoare_stableCopyOwnedFrame_assign _ _ (by decide) (by decide) (by decide))

/-- An active loop head supplies the concrete body's full precondition. -/
theorem hoare_stableCopy_active_body :
    Hoare (fun s => StableCopyLoopInv s ∧
      LoopActive (.cmp .less (.var .local (ofString "i"))
        (.var .local (ofString "nl"))) s)
      (.seq (.store (.op .add [.var .local (ofString "stable_lp"),
        .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))
      (fun r t => r = none → StableCopyLoopInv t) := by
  refine ⟨fun s hc hp hnt hr => ?_⟩
  obtain ⟨i, n, hi, hn⟩ := hp.1.2.1
  exact hoare_stableCopy_body_loop.run s hc
    ⟨stableCopyLoopInv_active s hp.1 hp.2, n, hn⟩ hnt hr

/-- An active copy step preserves both the loop invariant and its ownership frame. -/
theorem hoare_stableCopy_active_body_owned :
    Hoare (fun s => (StableCopyLoopInv s ∧ StableCopyOwnedFrame s) ∧
      LoopActive (.cmp .less (.var .local (ofString "i"))
        (.var .local (ofString "nl"))) s)
      (.seq (.store (.op .add [.var .local (ofString "stable_lp"),
        .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))
      (fun r t => r = none → StableCopyLoopInv t ∧ StableCopyOwnedFrame t) := by
  refine ⟨fun s hc hp hnt hr => ?_⟩
  exact ⟨hoare_stableCopy_active_body.run s hc ⟨hp.1.1, hp.2⟩ hnt hr,
    hoare_stableCopy_body_ownedFrame.run s hc
      ⟨stableCopyLoopInv_active s hp.1.1 hp.2, hp.1.2⟩ hnt hr⟩

/-- At an active loop head the concrete body restores the full loop invariant. -/
theorem hoare_stableCopy_body_active :
    Hoare (fun s => StableCopyLoopInv s ∧
      LoopActive (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl"))) s)
      (.seq (.store (.op .add [.var .local (ofString "stable_lp"),
        .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))
      (fun r t => r = none → StableCopyLoopInv t) := by
  apply hoare_stableCopy_body_loop.mono
  intro F s hp
  obtain ⟨i, n, hi, hn⟩ := hp.1.2.1
  exact ⟨stableCopyLoopInv_active s hp.1 hp.2, n, hn⟩

/-- The indexed copy store followed by the real increment preserves the invariant. -/
theorem hoare_stableCopy_body :
    Hoare StableCopyStorePre
      (.seq (.store (.op .add [.var .local (ofString "stable_lp"),
        .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))
      (fun r t => r = none → StableCopyInv t) := by
  apply Hoare.seq_fall hoare_stableCopy_store_for_increment
  apply Hoare.assign
  · intro F s v hp hv _
    exact hp v hv
  · intro F s hp hr
    cases hr

/-- The store/increment body consumes no clock; only the enclosing loop
iteration contributes to its bounded execution cost. -/
theorem stableCopy_body_bound :
    TerminatingProgBoundedOn StableCopyStorePre
      (.seq (.store (.op .add [.var .local (ofString "stable_lp"),
        .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))) 0 := by
  intro F s hc hp
  exact seq_bound_trans
    (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
    hoare_stableCopy_store_for_increment
    (by
      intro F t hc ht
      exact (TerminatingProgBoundedOn.of_clock
        (P := fun _ => True)
        (fun u => clock_assign u .local (ofString "i")
          (.op .add [.var .local (ofString "i"), .const 1]))) t hc trivial) s hc hp

/-- Bounded-loop assembly for the concrete store/increment body. The remaining
iteration obligation includes preservation of allocation separation. -/
theorem stableCopy_loop_bound_of_step
    (hstep : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      s.code = originalRuntimeCode → StableCopyLoopInv s →
      LoopActive (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl"))) s →
      let body : ProgHOL 64 := .seq
        (.store (.op .add [.var .local (ofString "stable_lp"),
          .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))
      ((evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none ∨
        (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = some .continue) →
      StableCopyLoopInv (evaluateHOLFiniteState (decClockHOLFinite s) body).2 ∧
        locN (evaluateHOLFiniteState (decClockHOLFinite s) body).2 "nl" -
          locN (evaluateHOLFiniteState (decClockHOLFinite s) body).2 "i" <
        locN s "nl" - locN s "i") :
    TerminatingProgBoundedOn StableCopyLoopInv
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl")))
        (.seq (.store (.op .add [.var .local (ofString "stable_lp"),
          .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))))
      ((2 ^ 28 + 1) * (0 + 1)) := by
  apply TerminatingProgBoundedOn.while_rank_active (fun s => locN s "nl" - locN s "i")
  · exact stableCopyLoopInv_decClock
  · intro F s hc hp
    exact stableCopy_body_bound s hc (stableCopyLoopInv_active s hp.1 hp.2)
  · intro F s hc hp ha
    exact stableCopyLoopInv_rank s hp
  · exact hstep

/-- The concrete stable-copy loop terminates under its full loop contract. -/
theorem stableCopy_loop_bound :
    TerminatingProgBoundedOn StableCopyLoopInv
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl")))
        (.seq (.store (.op .add [.var .local (ofString "stable_lp"),
          .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))))
      ((2 ^ 28 + 1) * (0 + 1)) := by
  apply stableCopy_loop_bound_of_step
  intro F s hc hp ha
  dsimp only
  intro hf
  let body : ProgHOL 64 := .seq
    (.store (.op .add [.var .local (ofString "stable_lp"),
      .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
    (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))
  have hinc : IncrBody (ofString "i") body := by
    dsimp [body]
    ptx_incr
  obtain ⟨i, n, hi, hn⟩ := hp.2.1
  obtain ⟨hnc, hnext⟩ := hinc.run (decClockHOLFinite s) i hi
  have hnone := hf.resolve_right hnc
  have hd := stableCopyLoopInv_decClock s hp
  have hactive := stableCopyLoopInv_active s hp ha
  have hpost := hoare_stableCopy_body_loop.run (decClockHOLFinite s) hc
    ⟨stableCopyStorePre_decClock s hactive, n, hn⟩ (by rw [hnone]; simp) hnone
  refine ⟨hpost, ?_⟩
  have hkeep := evaluate_avoidsLocal_flowing (ofString "nl") body (by decide)
    (decClockHOLFinite s) (Or.inl hnone)
  have hlen : locN (evaluateHOLFiniteState (decClockHOLFinite s) body).2 "nl" =
      locN s "nl" := by
    simp only [locN, hkeep]
    rfl
  have hidx : locN (evaluateHOLFiniteState (decClockHOLFinite s) body).2 "i" =
      (i.toNat + 1) % 2 ^ 64 := by
    simp [locN, hnext hnone, BitVec.toNat_add]
  have hil : locN s "i" = i.toNat := by simp [locN, hi]
  have hb := (stableLengthPost_length_bound s hp.1.1 hp.1.2.1).1
  have hai := hactive.2.1
  change locN (evaluateHOLFiniteState (decClockHOLFinite s) body).2 "nl" -
    locN (evaluateHOLFiniteState (decClockHOLFinite s) body).2 "i" < _
  rw [hlen, hidx, Nat.mod_eq_of_lt (by omega)]
  omega

/-- The concrete loop's budget is one clock tick per possible iteration,
plus the final guard check. -/
theorem stableCopy_loop_budget :
    TerminatingProgBoundedOn StableCopyLoopInv
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl")))
        (.seq (.store (.op .add [.var .local (ofString "stable_lp"),
          .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))))
      (2 ^ 28 + 1) := by
  intro F s hc hp
  simpa only [Nat.zero_add, Nat.mul_one] using stableCopy_loop_bound s hc hp

/-- Normal exit from the concrete copy loop establishes receipt readiness. -/
theorem hoare_stableCopy_loop_done_frame
    (Frame : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (hdec : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), Frame s → Frame (decClockHOLFinite s))
    (hframe : Hoare (fun s => StableCopyStorePre s ∧ Frame s)
      (.seq (.store (.op .add [.var .local (ofString "stable_lp"),
        .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))
      (fun r t => r = none → Frame t)) :
    Hoare (fun s => StableCopyLoopInv s ∧ Frame s)
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl")))
        (.seq (.store (.op .add [.var .local (ofString "stable_lp"),
          .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))))
      (fun r t => r = none → PtxReceiptsDone t ∧ Frame t ∧ StableCopyLoopInv t ∧
        evalAt t (.cmp .less (.var .local (ofString "i"))
          (.var .local (ofString "nl"))) = some (.val (.word 0))) := by
  let body : ProgHOL 64 := .seq
    (.store (.op .add [.var .local (ofString "stable_lp"),
      .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
    (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))
  have hinc : IncrBody (ofString "i") body := by dsimp [body]; ptx_incr
  refine ⟨fun {F} s hc hp _ hr => ?_⟩
  rcases hrun : evaluateHOLFiniteState s (.while
    (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl"))) body) with ⟨r, post⟩
  change (evaluateHOLFiniteState s (.while _ body)).1 = none at hr
  rw [hrun] at hr
  dsimp only at hr
  subst r
  suffices ∀ (k : Nat) (st : PanSemStateFiniteExact 64 F),
      st.clock = k → st.code = originalRuntimeCode → (StableCopyLoopInv st ∧ Frame st) →
      evaluateHOLFiniteState st (.while
        (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl"))) body) =
        (none, post) → PtxReceiptsDone post ∧ Frame post ∧ StableCopyLoopInv post ∧
          evalAt post (.cmp .less (.var .local (ofString "i"))
            (.var .local (ofString "nl"))) = some (.val (.word 0)) from
    this s.clock s rfl hc hp hrun
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro st hk hc hp hrun
    rw [evaluateHOLFiniteState_while_total] at hrun
    split at hrun
    · rename_i w hw
      split at hrun
      · rename_i hnz
        split at hrun
        · simp at hrun
        · dsimp only at hrun
          rw [fixClockHOLFinite_evaluateState] at hrun
          have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) body
          have hmeta := (evaluateHOLFiniteState_metadata (decClockHOLFinite st) body).1
          have hnb := InitECandidate.Solver.GuestUniformClockBound.evaluate_noTopBreak
            body (by decide) (decClockHOLFinite st)
          obtain ⟨i, n, hi, hn⟩ := hp.1.2.1
          obtain ⟨hnc, _⟩ := hinc.run (decClockHOLFinite st) i hi
          have ha := stableCopyLoopInv_active st hp.1 ⟨w, hw, hnz⟩
          rcases hb : evaluateHOLFiniteState (decClockHOLFinite st) body with ⟨r, mid⟩
          rw [hb] at hrun hrem hmeta hnb hnc
          have hlt : mid.clock < k := by
            change mid.clock ≤ st.clock - 1 at hrem
            omega
          cases r with
          | none =>
            have hm := hoare_stableCopy_body_loop.run (decClockHOLFinite st) hc
              ⟨stableCopyStorePre_decClock st ha, n, hn⟩
              (by change (evaluateHOLFiniteState _ body).1 ≠ _; rw [hb]; simp)
              (by change (evaluateHOLFiniteState _ body).1 = _; rw [hb])
            change StableCopyLoopInv (evaluateHOLFiniteState _ body).2 at hm
            rw [hb] at hm
            have hf := hframe.run (decClockHOLFinite st) hc
              ⟨stableCopyStorePre_decClock st ha, hdec st hp.2⟩
              (by change (evaluateHOLFiniteState _ body).1 ≠ _; rw [hb]; simp)
              (by change (evaluateHOLFiniteState _ body).1 = _; rw [hb])
            change Frame (evaluateHOLFiniteState _ body).2 at hf
            rw [hb] at hf
            exact ih mid.clock hlt mid rfl (hmeta.trans hc) ⟨hm, hf⟩ hrun
          | some r =>
            cases r with
            | «continue» => exact absurd rfl hnc
            | «break» => exact absurd rfl hnb
            | _ => simp at hrun
      · rename_i hz
        have hw0 : w = 0 := Classical.not_not.mp hz
        subst w
        simp at hrun
        obtain ⟨_, rfl⟩ := hrun
        exact ⟨stableCopyLoopInv_done _ hp.1 hw, hp.2, hp.1, hw⟩
    · simp at hrun

/-- The complete copy loop retains its coherent ownership frame. -/
theorem hoare_stableCopy_loop_ownedFrame :
    Hoare (fun s => StableCopyLoopInv s ∧ StableCopyOwnedFrame s)
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl")))
        (.seq (.store (.op .add [.var .local (ofString "stable_lp"),
          .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))))
      (fun r t => r = none → PtxReceiptsDone t ∧ StableCopyOwnedFrame t) := by
  have hf := hoare_stableCopy_loop_done_frame StableCopyOwnedFrame
    (fun s hp => stableCopyOwnedFrame_with_locals s s.locals (s.clock - 1) rfl rfl rfl hp)
    hoare_stableCopy_body_ownedFrame
  exact ⟨fun s hc hp hnt hr => let h := hf.run s hc hp hnt hr; ⟨h.1, h.2.1⟩⟩

/-- Normal copy-loop exit establishes ownership of the completed stable list. -/
theorem hoare_stableCopy_loop_owned :
    Hoare (fun s => StableCopyLoopInv s ∧ StableCopyOwnedFrame s)
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl")))
        (.seq (.store (.op .add [.var .local (ofString "stable_lp"),
          .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))))
      (fun r t => r = none → PtxReceiptsDone t ∧ LogsWorldOwned t (locN t "stable_logs") ∧
        locN t "stable_logs" ≠ 0 ∧
        ∃ w : BitVec 64, t.locals.lookup (ofString "stable_logs") = some (.val (.word w))) := by
  have hf := hoare_stableCopy_loop_done_frame StableCopyOwnedFrame
    (fun s hp => stableCopyOwnedFrame_with_locals s s.locals (s.clock - 1) rfl rfl rfl hp)
    hoare_stableCopy_body_ownedFrame
  refine ⟨fun s hc hp hnt hr => ?_⟩
  have h := hf.run s hc hp hnt hr
  have hd := stableCopyLoopInv_done_owned _ h.2.2.1 h.2.1 h.2.2.2
  exact ⟨hd.1, hd.2, stableCopyInv_stable_local _ h.2.2.1.1⟩

/-- The unframed copy-loop rule is the trivial-frame specialization. -/
theorem hoare_stableCopy_loop_done :
    Hoare StableCopyLoopInv
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl")))
        (.seq (.store (.op .add [.var .local (ofString "stable_lp"),
          .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))))
      (fun r t => r = none → PtxReceiptsDone t) := by
  have hf := hoare_stableCopy_loop_done_frame (fun _ => True)
    (fun _ _ => True.intro) ⟨fun _ _ _ _ _ => True.intro⟩
  exact ⟨fun s hc hp hnt hr => (hf.run s hc ⟨hp, True.intro⟩ hnt hr).1⟩

/-- Compose the completed stable-copy loop with the receipt continuation. -/
theorem stableCopy_loop_cut {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn PtxReceiptsDone tail b) :
    TerminatingProgBoundedOn StableCopyLoopInv
      (.seq
        (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl")))
          (.seq (.store (.op .add [.var .local (ofString "stable_lp"),
            .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
            (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))))
        tail) (2 ^ 28 + 1 + b) := by
  intro F s hc hp
  exact seq_bound_trans stableCopy_loop_budget hoare_stableCopy_loop_done htail s hc hp

/-- The ownership-preserving loop composes with a stronger receipt continuation
at the same concrete loop budget. -/
theorem stableCopy_loop_owned_cut {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn
      (fun s => PtxReceiptsDone s ∧ LogsWorldOwned s (locN s "stable_logs") ∧
        locN s "stable_logs" ≠ 0 ∧
        ∃ w : BitVec 64, s.locals.lookup (ofString "stable_logs") = some (.val (.word w))) tail b) :
    TerminatingProgBoundedOn (fun s => StableCopyLoopInv s ∧ StableCopyOwnedFrame s)
      (.seq
        (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl")))
          (.seq (.store (.op .add [.var .local (ofString "stable_lp"),
            .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
            (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))))
        tail) (2 ^ 28 + 1 + b) := by
  intro F s hc hp
  exact seq_bound_trans (fun t ht h => stableCopy_loop_budget t ht h.1)
    hoare_stableCopy_loop_owned htail s hc hp

/-- Counter initialization composes with any bounded full-loop continuation. -/
theorem stableCopy_init_spatial_cut {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn StableCopyLoopInv tail b) :
    TerminatingProgBoundedOn (fun s => StableLengthPost s ∧ locN s "logs" ≠ 0 ∧
      WordsOK s (locN s "stable_logs", 24) ∧ Allocated s (locN s "stable_logs", 24) ∧
      locN s "nl" ≤ locN s "stable_log_cap" ∧ StableCopySpatial s ∧
      ∃ n p q : BitVec 64,
        s.locals.lookup (ofString "nl") = some (.val (.word n)) ∧
        s.locals.lookup (ofString "lp") = some (.val (.word p)) ∧
        s.locals.lookup (ofString "stable_lp") = some (.val (.word q)) ∧
        q.toNat = memW s (locN s "stable_logs"))
      (.seq (.assign .local (ofString "i") (.const 0)) tail) b := by
  rw [← Nat.zero_add b]
  intro F s hc hp
  refine seq_bound_trans (P := fun s => StableLengthPost s ∧ locN s "logs" ≠ 0 ∧
      WordsOK s (locN s "stable_logs", 24) ∧ Allocated s (locN s "stable_logs", 24) ∧
      locN s "nl" ≤ locN s "stable_log_cap" ∧ StableCopySpatial s ∧
      ∃ n p q : BitVec 64,
        s.locals.lookup (ofString "nl") = some (.val (.word n)) ∧
        s.locals.lookup (ofString "lp") = some (.val (.word p)) ∧
        s.locals.lookup (ofString "stable_lp") = some (.val (.word q)) ∧
        q.toNat = memW s (locN s "stable_logs"))
    ?_ hoare_stableCopy_init_spatial htail s hc hp
  intro F' t hcode hpre hclock
  have ht := clock_assign t .local (ofString "i") (.const 0)
  exact ⟨by omega, by omega⟩

/-- Counter initialization retains the ownership frame for an owned loop. -/
theorem stableCopy_init_owned_cut {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn
      (fun s => StableCopyLoopInv s ∧ StableCopyOwnedFrame s) tail b) :
    TerminatingProgBoundedOn (fun s =>
      (StableLengthPost s ∧ locN s "logs" ≠ 0 ∧
        WordsOK s (locN s "stable_logs", 24) ∧ Allocated s (locN s "stable_logs", 24) ∧
        locN s "nl" ≤ locN s "stable_log_cap" ∧ StableCopySpatial s ∧
        ∃ n p q : BitVec 64,
          s.locals.lookup (ofString "nl") = some (.val (.word n)) ∧
          s.locals.lookup (ofString "lp") = some (.val (.word p)) ∧
          s.locals.lookup (ofString "stable_lp") = some (.val (.word q)) ∧
          q.toNat = memW s (locN s "stable_logs")) ∧ StableCopyOwnedFrame s)
      (.seq (.assign .local (ofString "i") (.const 0)) tail) b := by
  have hf := hoare_stableCopyOwnedFrame_assign (ofString "i") (.const 0)
    (by decide) (by decide) (by decide)
  intro F s hc hp
  have hi := hoare_stableCopy_init_spatial
  have hj : Hoare (fun s =>
      (StableLengthPost s ∧ locN s "logs" ≠ 0 ∧
        WordsOK s (locN s "stable_logs", 24) ∧ Allocated s (locN s "stable_logs", 24) ∧
        locN s "nl" ≤ locN s "stable_log_cap" ∧ StableCopySpatial s ∧
        ∃ n p q : BitVec 64,
          s.locals.lookup (ofString "nl") = some (.val (.word n)) ∧
          s.locals.lookup (ofString "lp") = some (.val (.word p)) ∧
          s.locals.lookup (ofString "stable_lp") = some (.val (.word q)) ∧
          q.toNat = memW s (locN s "stable_logs")) ∧ StableCopyOwnedFrame s)
      (.assign .local (ofString "i") (.const 0))
      (fun r t => r = none → StableCopyLoopInv t ∧ StableCopyOwnedFrame t) :=
    ⟨fun t ht h hnt hr => ⟨hi.run t ht h.1 hnt hr, hf.run t ht h.2 hnt hr⟩⟩
  simpa only [Nat.zero_add] using seq_bound_trans (a := 0)
    (fun t _ _ _ => by
      have ht := clock_assign t .local (ofString "i") (.const 0)
      exact ⟨by omega, by omega⟩) hj htail s hc hp

/-- The concrete right-associated setup adds no clock cost before a bounded
copy-loop continuation. -/
theorem stableCopy_backing_init_cut {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn StableCopyLoopInv tail b) :
    TerminatingProgBoundedOn (fun s => StableLengthPost s ∧ locN s "logs" ≠ 0 ∧
      WordsOK s (locN s "stable_logs", 24) ∧ Allocated s (locN s "stable_logs", 24) ∧
      locN s "nl" ≤ locN s "stable_log_cap" ∧ StableCopySpatial s ∧
      WordAt s (locN s "stable_logs") ∧ ∃ n p w : BitVec 64,
        s.locals.lookup (ofString "nl") = some (.val (.word n)) ∧
        s.locals.lookup (ofString "lp") = some (.val (.word p)) ∧
        s.locals.lookup (ofString "stable_logs") = some (.val (.word w)))
      (.seq (.assign .local (ofString "stable_lp")
        (.load .one (.var .local (ofString "stable_logs"))))
        (.seq (.assign .local (ofString "i") (.const 0)) tail)) b := by
  have hi : Hoare (fun s => StableCopyLoopInv
      (setVarHOLFinite (ofString "i") (.val (.word 0)) s))
      (.assign .local (ofString "i") (.const 0))
      (fun r t => r = none → StableCopyLoopInv t) := by
    apply Hoare.assign
    · intro F s v hp hv _
      have hv' : v = .val (.word 0) := by simpa [evalAt, evalHOLExact] using hv.symm
      subst v
      exact hp
    · intro F s hp hr
      cases hr
  intro F s hc hp
  have hinit : TerminatingProgBoundedOn (fun s => StableCopyLoopInv
      (setVarHOLFinite (ofString "i") (.val (.word 0)) s))
      (.seq (.assign .local (ofString "i") (.const 0)) tail) (0 + b) := by
    intro G t ht hq
    exact seq_bound_trans (fun u _ _ _ => by
      have hu := clock_assign u .local (ofString "i") (.const 0)
      exact ⟨by omega, by omega⟩) hi htail t ht hq
  simpa only [Nat.zero_add] using seq_bound_trans (a := 0)
    (fun u _ _ _ => by
      have hu := clock_assign u .local (ofString "stable_lp")
        (.load .one (.var .local (ofString "stable_logs")))
      exact ⟨by omega, by omega⟩)
    hoare_stableCopy_backing_entry hinit s hc hp

/-- Complete backing/counter setup followed by copying and a receipt continuation. -/
theorem stableCopy_setup_loop_cut {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn PtxReceiptsDone tail b) :
    TerminatingProgBoundedOn (fun s => StableLengthPost s ∧ locN s "logs" ≠ 0 ∧
      WordsOK s (locN s "stable_logs", 24) ∧ Allocated s (locN s "stable_logs", 24) ∧
      locN s "nl" ≤ locN s "stable_log_cap" ∧ StableCopySpatial s ∧
      WordAt s (locN s "stable_logs") ∧ ∃ n p w : BitVec 64,
        s.locals.lookup (ofString "nl") = some (.val (.word n)) ∧
        s.locals.lookup (ofString "lp") = some (.val (.word p)) ∧
        s.locals.lookup (ofString "stable_logs") = some (.val (.word w)))
      (.seq (.assign .local (ofString "stable_lp")
        (.load .one (.var .local (ofString "stable_logs"))))
        (.seq (.assign .local (ofString "i") (.const 0))
          (.seq (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl")))
            (.seq (.store (.op .add [.var .local (ofString "stable_lp"),
              .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
              (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))))
            tail))) (2 ^ 28 + 1 + b) := by
  intro F s hc hp
  exact stableCopy_backing_init_cut (stableCopy_loop_cut htail) s hc hp

/-- The source-level backing declaration and counter initialization enter copying. -/
theorem stableCopy_backing_decl_cut {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn StableCopyLoopInv tail b) :
    TerminatingProgBoundedOn (fun s => StableLengthPost s ∧ locN s "logs" ≠ 0 ∧
      WordsOK s (locN s "stable_logs", 24) ∧ Allocated s (locN s "stable_logs", 24) ∧
      locN s "nl" ≤ locN s "stable_log_cap" ∧ StableCopySpatial s ∧
      WordAt s (locN s "stable_logs") ∧ ∃ n p w : BitVec 64,
        s.locals.lookup (ofString "nl") = some (.val (.word n)) ∧
        s.locals.lookup (ofString "lp") = some (.val (.word p)) ∧
        s.locals.lookup (ofString "stable_logs") = some (.val (.word w)))
      (.dec (ofString "stable_lp") .one
        (.load .one (.op .add [.var .local (ofString "stable_logs"), .const 0]))
        (.seq (.assign .local (ofString "i") (.const 0)) tail)) b := by
  have hi : TerminatingProgBoundedOn (fun s => StableCopyLoopInv
      (setVarHOLFinite (ofString "i") (.val (.word 0)) s))
      (.seq (.assign .local (ofString "i") (.const 0)) tail) b := by
    intro F s hc hp
    have hb := seq_bound_trans (a := 0) (fun u _ _ _ => by
      have hu := clock_assign u .local (ofString "i") (.const 0)
      exact ⟨by omega, by omega⟩) hoare_stableCopy_zero_entry htail s hc hp
    simpa only [Nat.zero_add] using hb
  intro G t ht hpre
  refine dec_bound_trans (P := fun s => StableLengthPost s ∧ locN s "logs" ≠ 0 ∧
      WordsOK s (locN s "stable_logs", 24) ∧ Allocated s (locN s "stable_logs", 24) ∧
      locN s "nl" ≤ locN s "stable_log_cap" ∧ StableCopySpatial s ∧
      WordAt s (locN s "stable_logs") ∧ ∃ n p w : BitVec 64,
        s.locals.lookup (ofString "nl") = some (.val (.word n)) ∧
        s.locals.lookup (ofString "lp") = some (.val (.word p)) ∧
        s.locals.lookup (ofString "stable_logs") = some (.val (.word w)))
    (Q := fun s => StableCopyLoopInv
    (setVarHOLFinite (ofString "i") (.val (.word 0)) s)) ?_ hi t ht hpre
  intro F s v hp he
  obtain ⟨hp, hz, hh, ha, hc, hs, hword, n, p, w, hn, hl, hw⟩ := hp
  apply stableCopyLoopInv_backing_init s hp hz hh ha hc hs n p w v hn hl hw hword
  simpa [evalAt, evalHOLExact, hw, valueIsWord, valueWord, evalListHOLExact,
    wordOpHOL, wordOp] using he

/-- The source-level backing declaration retains ownership for the copy loop. -/
theorem stableCopy_backing_decl_owned_cut {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn
      (fun s => StableCopyLoopInv s ∧ StableCopyOwnedFrame s) tail b) :
    TerminatingProgBoundedOn (fun s => (StableLengthPost s ∧ locN s "logs" ≠ 0 ∧
      WordsOK s (locN s "stable_logs", 24) ∧ Allocated s (locN s "stable_logs", 24) ∧
      locN s "nl" ≤ locN s "stable_log_cap" ∧ StableCopySpatial s ∧
      WordAt s (locN s "stable_logs") ∧ ∃ n p w : BitVec 64,
        s.locals.lookup (ofString "nl") = some (.val (.word n)) ∧
        s.locals.lookup (ofString "lp") = some (.val (.word p)) ∧
        s.locals.lookup (ofString "stable_logs") = some (.val (.word w))) ∧
      StableCopyOwnedFrame s)
      (.dec (ofString "stable_lp") .one
        (.load .one (.op .add [.var .local (ofString "stable_logs"), .const 0]))
        (.seq (.assign .local (ofString "i") (.const 0)) tail)) b := by
  have hf := hoare_stableCopyOwnedFrame_assign (ofString "i") (.const 0)
    (by decide) (by decide) (by decide)
  have hi : TerminatingProgBoundedOn (fun s =>
      StableCopyLoopInv (setVarHOLFinite (ofString "i") (.val (.word 0)) s) ∧
      StableCopyOwnedFrame s)
      (.seq (.assign .local (ofString "i") (.const 0)) tail) b := by
    intro F s hc hp
    have hj : Hoare (fun s =>
        StableCopyLoopInv (setVarHOLFinite (ofString "i") (.val (.word 0)) s) ∧
        StableCopyOwnedFrame s) (.assign .local (ofString "i") (.const 0))
        (fun r t => r = none → StableCopyLoopInv t ∧ StableCopyOwnedFrame t) :=
      ⟨fun t ht h hnt hr => ⟨hoare_stableCopy_zero_entry.run t ht h.1 hnt hr,
        hf.run t ht h.2 hnt hr⟩⟩
    simpa only [Nat.zero_add] using seq_bound_trans (a := 0) (fun u _ _ _ => by
      have hu := clock_assign u .local (ofString "i") (.const 0)
      exact ⟨by omega, by omega⟩) hj htail s hc hp
  intro G t ht hpre
  refine dec_bound_trans (P := fun s => (StableLengthPost s ∧ locN s "logs" ≠ 0 ∧
      WordsOK s (locN s "stable_logs", 24) ∧ Allocated s (locN s "stable_logs", 24) ∧
      locN s "nl" ≤ locN s "stable_log_cap" ∧ StableCopySpatial s ∧
      WordAt s (locN s "stable_logs") ∧ ∃ n p w : BitVec 64,
        s.locals.lookup (ofString "nl") = some (.val (.word n)) ∧
        s.locals.lookup (ofString "lp") = some (.val (.word p)) ∧
        s.locals.lookup (ofString "stable_logs") = some (.val (.word w))) ∧
      StableCopyOwnedFrame s) (Q := fun s =>
      StableCopyLoopInv (setVarHOLFinite (ofString "i") (.val (.word 0)) s) ∧
      StableCopyOwnedFrame s) ?_ hi t ht hpre
  intro F s v hp he
  obtain ⟨⟨hp, hz, hh, ha, hc, hs, hword, n, p, w, hn, hl, hw⟩, hframe⟩ := hp
  constructor
  · apply stableCopyLoopInv_backing_init s hp hz hh ha hc hs n p w v hn hl hw hword
    simpa [evalAt, evalHOLExact, hw, valueIsWord, valueWord, evalListHOLExact,
      wordOpHOL, wordOp] using he
  · apply stableCopyOwnedFrame_with_locals s _ s.clock _ _ _ hframe
    all_goals simp [HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "stable_lp" ≠ ofString "logs" by decide,
      show ofString "stable_lp" ≠ ofString "stable_logs" by decide,
      show ofString "stable_lp" ≠ ofString "stable_log_cap" by decide]

/-- The concrete length store, setup, and copy loop compose with a receipt tail. -/
theorem stable_length_setup_loop_cut {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn PtxReceiptsDone tail b) :
    TerminatingProgBoundedOn (fun s => (StableLengthPre s ∧
      (∃ S Nd, WorldTypedWith s S Nd ∧ LogsLiveOwned s S Nd (locN s "logs") ∧
        (∀ o ∈ worldOwned s S Nd, Disj (locN s "stable_logs", 24) o) ∧
        (∀ o ∈ worldOwned s S Nd,
          Disj (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") o)) ∧
      Disj (locN s "logs", 24)
        (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
      Disj (locN s "stable_logs", 24)
        (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
      Disj (memW s (locN s "logs"), 8 * memW s (locN s "logs" + 8))
        (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
      ∀ j, j < memW s (locN s "logs" + 8) →
        Disj (memW s (memW s (locN s "logs") + 8 * j), 40)
          (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap")) ∧
      locN s "logs" ≠ 0 ∧ WordsOK s (locN s "stable_logs", 24) ∧
      ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p)))
      (.seq (.store (.op .add [.var .local (ofString "stable_logs"), .const 8])
        (.var .local (ofString "nl")))
        (.seq (.assign .local (ofString "stable_lp")
          (.load .one (.var .local (ofString "stable_logs"))))
          (.seq (.assign .local (ofString "i") (.const 0))
            (.seq (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl")))
              (.seq (.store (.op .add [.var .local (ofString "stable_lp"),
                .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
                (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))))
              tail)))) (2 ^ 28 + 1 + b) := by
  intro F s hc hp
  rw [← Nat.zero_add (2 ^ 28 + 1 + b)]
  refine seq_bound_trans ?_ hoare_stable_length_copy_ready
    (stableCopy_setup_loop_cut htail) s hc hp
  intro G t _ _ hclock
  have ht := clock_store t (.op .add [.var .local (ofString "stable_logs"), .const 8])
    (.var .local (ofString "nl"))
  exact ⟨by omega, by omega⟩

/-- The actual length store and scoped backing declaration precede the copy loop. -/
theorem stable_length_decl_loop_cut {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn PtxReceiptsDone tail b) :
    TerminatingProgBoundedOn (fun s => (StableLengthPre s ∧
      (∃ S Nd, WorldTypedWith s S Nd ∧ LogsLiveOwned s S Nd (locN s "logs") ∧
        (∀ o ∈ worldOwned s S Nd, Disj (locN s "stable_logs", 24) o) ∧
        (∀ o ∈ worldOwned s S Nd,
          Disj (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") o)) ∧
      Disj (locN s "logs", 24)
        (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
      Disj (locN s "stable_logs", 24)
        (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
      Disj (memW s (locN s "logs"), 8 * memW s (locN s "logs" + 8))
        (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
      ∀ j, j < memW s (locN s "logs" + 8) →
        Disj (memW s (memW s (locN s "logs") + 8 * j), 40)
          (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap")) ∧
      locN s "logs" ≠ 0 ∧ WordsOK s (locN s "stable_logs", 24) ∧
      ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p)))
      (spinePlug 4 (spineAt 133 ptxCode) tail) (2 ^ 28 + 1 + b) := by
  have he : spinePlug 4 (spineAt 133 ptxCode) tail =
      .seq (.store (.op .add [.var .local (ofString "stable_logs"), .const 8])
        (.var .local (ofString "nl")))
        (.dec (ofString "stable_lp") .one
          (.load .one (.op .add [.var .local (ofString "stable_logs"), .const 0]))
          (.seq (.assign .local (ofString "i") (.const 0))
            (.seq (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl")))
              (.seq (.store (.op .add [.var .local (ofString "stable_lp"),
                .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
                (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))))
              tail))) := by
    unfold ptxCode phase4LogCopySrc
    rfl
  rw [he]
  intro F s hc hp
  rw [← Nat.zero_add (2 ^ 28 + 1 + b)]
  refine seq_bound_trans ?_ hoare_stable_length_copy_ready
    (stableCopy_backing_decl_cut (stableCopy_loop_cut htail)) s hc hp
  intro G t _ _ hclock
  have ht := clock_store t (.op .add [.var .local (ofString "stable_logs"), .const 8])
    (.var .local (ofString "nl"))
  exact ⟨by omega, by omega⟩

/-- Length storage and scoped copying retain ownership for the receipt tail. -/
theorem stable_length_decl_loop_owned_cut {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn
      (fun s => PtxReceiptsDone s ∧ LogsWorldOwned s (locN s "stable_logs") ∧
        locN s "stable_logs" ≠ 0 ∧
        ∃ w : BitVec 64, s.locals.lookup (ofString "stable_logs") = some (.val (.word w))) tail b) :
    TerminatingProgBoundedOn (fun s => (StableLengthPre s ∧ StableCopyOwnedFrame s ∧
      Disj (locN s "logs", 24)
        (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
      Disj (locN s "stable_logs", 24)
        (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
      Disj (memW s (locN s "logs"), 8 * memW s (locN s "logs" + 8))
        (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
      ∀ j, j < memW s (locN s "logs" + 8) →
        Disj (memW s (memW s (locN s "logs") + 8 * j), 40)
          (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap")) ∧
      locN s "logs" ≠ 0 ∧ WordsOK s (locN s "stable_logs", 24) ∧
      ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p)))
      (spinePlug 4 (spineAt 133 ptxCode) tail) (2 ^ 28 + 1 + b) := by
  have he : spinePlug 4 (spineAt 133 ptxCode) tail =
    (.seq (.store (.op .add [.var .local (ofString "stable_logs"), .const 8])
      (.var .local (ofString "nl")))
      (.dec (ofString "stable_lp") .one
        (.load .one (.op .add [.var .local (ofString "stable_logs"), .const 0]))
        (.seq (.assign .local (ofString "i") (.const 0))
          (.seq (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl")))
            (.seq (.store (.op .add [.var .local (ofString "stable_lp"),
              .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
              (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))))
            tail)))) := by
    unfold ptxCode phase4LogCopySrc
    rfl
  rw [he]
  intro F s hc hp
  simpa only [Nat.zero_add] using seq_bound_trans (a := 0)
    (fun t _ _ _ => by
      have ht := clock_store t (.op .add [.var .local (ofString "stable_logs"), .const 8])
        (.var .local (ofString "nl"))
      exact ⟨by omega, by omega⟩)
    hoare_stable_length_owned_copy_ready
    (stableCopy_backing_decl_owned_cut (stableCopy_loop_owned_cut htail)) s hc hp

/-- Package the length-write framing facts into the complete copy setup contract. -/
theorem stable_length_copy_setup_ready {F : Type} (s : PanSemStateFiniteExact 64 F)
    (mem' : BitVec 64 → HolWordLab 64) (w p : BitVec 64)
    (hp : StableLengthPre s) (hz : locN s "logs" ≠ 0)
    (hh : WordsOK s (locN s "stable_logs", 24))
    (hc : locN s "nl" ≤ locN s "stable_log_cap")
    (hl : s.locals.lookup (ofString "lp") = some (.val (.word p)))
    (he : mem' (BitVec.ofNat 64 (locN s "stable_logs" + 8)) = .word w)
    (hm : ∀ a, a ≠ BitVec.ofNat 64 (locN s "stable_logs" + 8) → mem' a = s.memory a)
    (hpost : StableLengthPost {s with memory := mem'})
    (hs : StableCopySpatial {s with memory := mem'}) :
    let t := {s with memory := mem'}
    StableLengthPost t ∧ locN t "logs" ≠ 0 ∧
      WordsOK t (locN t "stable_logs", 24) ∧ Allocated t (locN t "stable_logs", 24) ∧
      locN t "nl" ≤ locN t "stable_log_cap" ∧ StableCopySpatial t ∧
      WordAt t (locN t "stable_logs") ∧ ∃ n p w : BitVec 64,
        t.locals.lookup (ofString "nl") = some (.val (.word n)) ∧
        t.locals.lookup (ofString "lp") = some (.val (.word p)) ∧
        t.locals.lookup (ofString "stable_logs") = some (.val (.word w)) := by
  obtain ⟨hh', ha', hw'⟩ := stable_length_store_header_ready s mem' w he hm hh hp.2.1
  exact ⟨hpost, hz, hh', ha', hc, hs, hw', stableLengthPre_memory_operands s hp mem' p hl⟩

/-- After a framed length write, setup and copying reach any bounded receipt
continuation with the concrete copy-loop budget. -/
theorem stable_length_copy_continuation {F : Type} (s : PanSemStateFiniteExact 64 F)
    (mem' : BitVec 64 → HolWordLab 64) (w p : BitVec 64)
    (hp : StableLengthPre s) (hz : locN s "logs" ≠ 0)
    (hh : WordsOK s (locN s "stable_logs", 24))
    (hc : locN s "nl" ≤ locN s "stable_log_cap")
    (hl : s.locals.lookup (ofString "lp") = some (.val (.word p)))
    (he : mem' (BitVec.ofNat 64 (locN s "stable_logs" + 8)) = .word w)
    (hm : ∀ a, a ≠ BitVec.ofNat 64 (locN s "stable_logs" + 8) → mem' a = s.memory a)
    (hpost : StableLengthPost {s with memory := mem'})
    (hs : StableCopySpatial {s with memory := mem'})
    (hcode : s.code = originalRuntimeCode) {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn PtxReceiptsDone tail b) :
    TerminatingRunBounded {s with memory := mem'}
      (.seq (.assign .local (ofString "stable_lp")
        (.load .one (.var .local (ofString "stable_logs"))))
        (.seq (.assign .local (ofString "i") (.const 0))
          (.seq (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl")))
            (.seq (.store (.op .add [.var .local (ofString "stable_lp"),
              .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
              (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))))
            tail))) (2 ^ 28 + 1 + b) := by
  exact stableCopy_setup_loop_cut htail _ hcode
    (stable_length_copy_setup_ready s mem' w p hp hz hh hc hl he hm hpost hs)

/-- An active separated copy state can run the entire remaining loop and
then any receipt-ready continuation. -/
theorem stableCopy_active_loop_cut {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn PtxReceiptsDone tail b) :
    TerminatingProgBoundedOn StableCopyStorePre
      (.seq
        (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl")))
          (.seq (.store (.op .add [.var .local (ofString "stable_lp"),
            .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
            (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))))
        tail) (2 ^ 28 + 1 + b) := by
  intro F s hc hp
  exact stableCopy_loop_cut htail s hc (stableCopyLoopInv_of_storePre s hp)

/-- Continue from the actual copy body without adding to the tail budget. -/
theorem stableCopy_body_cut {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn StableCopyInv tail b) :
    TerminatingProgBoundedOn StableCopyStorePre
      (.seq (.seq (.store (.op .add [.var .local (ofString "stable_lp"),
        .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])) ) tail) b := by
  intro F s hc hp
  simpa only [Nat.zero_add] using
    (seq_bound_trans stableCopy_body_bound hoare_stableCopy_body htail s hc hp)

/-- The termination measure decreases across both the memory write and the
counter assignment; the write cannot alter either counter local. -/
theorem stableCopyInv_store_increment_decreases {F : Type}
    (s : PanSemStateFiniteExact 64 F) (mem' : BitVec 64 → HolWordLab 64)
    (w : BitVec 64) (v : ValueHOL 64) (hp : StableCopyInv s)
    (hw : s.locals.lookup (ofString "i") = some (.val (.word w)))
    (hi : locN s "i" < locN s "nl")
    (he : evalAt {s with memory := mem'}
      (.op .add [.var .local (ofString "i"), .const 1]) = some v) :
    locN (setVarHOLFinite (ofString "i") v {s with memory := mem'}) "nl" -
        locN (setVarHOLFinite (ofString "i") v {s with memory := mem'}) "i" <
      locN s "nl" - locN s "i" := by
  have he' : evalAt s (.op .add [.var .local (ofString "i"), .const 1]) = some v := by
    simpa only [evalAt, evalHOLExact, evalListHOLExact] using he
  exact stableCopyInv_increment_decreases s w v hp hw hi he'

theorem stable_header_disj_source {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {p : Nat} (hA : ArenaOK s) (hPost : ArenaOK post)
    (hh : FreshBlock s post p 24) (hp : Phase4LogPointersReady s) :
    Disj (p, 24) (locN s "logs", 24) := by
  have hl := hp.1.1.2.1
  rcases hl with hz | hl
  · exact False.elim (hp.1.2.2 hz)
  · exact hh.disj_allocated hA hPost hl.2.1

/-- Fresh stable storage avoids every source cell that the stable-copy loop
will read, including a scratch-resident source array. -/
theorem fresh_stable_disj_source {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {p n : Nat} (hA : ArenaOK s) (hPost : ArenaOK post)
    (hf : FreshBlock s post p n) (hn : n % 8 = 0) (hp : Phase4LogPointersReady s) :
    Disj (p, n) (locN s "logs", 24) ∧
      Disj (p, n) (memW s (locN s "logs"), 8 * memW s (locN s "logs" + 8)) ∧
      ∀ i, i < memW s (locN s "logs" + 8) →
        Disj (p, n) (memW s (memW s (locN s "logs") + 8 * i), 40) := by
  have hl := hp.1.1.2.1.resolve_left hp.1.2.2
  obtain ⟨a, b, _, _, _, _, S, Nd, _, ho⟩ := hp.1.1.2.2.2
  have hround : (n + 7) / 8 * 8 = n := by omega
  have hd : ∀ i, Allocated s i → Disj (p, n) i := by
    intro i hi
    simpa only [hround] using hf.disj_allocated hA hPost hi
  refine ⟨hd _ hl.2.1, hd _ (ho hp.1.2.2).1, ?_⟩
  intro i hi
  exact hd _ (Or.inl (hl.2.2.2.2 i hi).2.2.1)

theorem stable_length_cell_disj {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hA : ArenaOK s) (hh : Allocated s (locN s "stable_logs", 24))
    {i : Ivl} (hd : Disj i (locN s "stable_logs", 24)) :
    Disj i ((BitVec.ofNat 64 (locN s "stable_logs" + 8)).toNat, 8) := by
  apply disj_of_inside_right ?_ hd
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (stable_length_address_bound s hA hh).1]
  constructor <;> dsimp <;> omega

/-- Both allocations returned by the stable-list constructor are separated
from the source header, backing cells, and entry records at call entry. -/
theorem lst_new_stable_source_separation (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    ∃ w : BitVec 64, v = .val (.word w) ∧
      ∀ a ∈ [(w.toNat, 24), (memW post w.toNat, 8 * locN s "stable_log_cap")],
        Disj a (locN s "logs", 24) ∧
        Disj a (memW s (locN s "logs"), 8 * memW s (locN s "logs" + 8)) ∧
        ∀ i, i < memW s (locN s "logs" + 8) →
          Disj a (memW s (memW s (locN s "logs") + 8 * i), 40) := by
  obtain ⟨w, hv, hh, hb, _⟩ := lst_new_stable_fresh h s vs body callee ret v post hc hp ha hl hr
  have hw := funSpec_at_lookup h.wk_lst_new s hc vs body callee ret hl
    (worldOK_callEntry hp.1.1.1.1.1.1 callee) (by rw [hr]; simp)
  rw [hr] at hw
  have hpost := (hw (Or.inl ⟨v, rfl⟩)).1
  refine ⟨w, hv, ?_⟩
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact fresh_stable_disj_source hp.1.1.1.1.1.1.1.2 hpost.2 hh (by decide) hp.1
  · exact fresh_stable_disj_source hp.1.1.1.1.1.1.1.2 hpost.2 hb (by omega) hp.1

/-- Transport fresh allocation separation to the source array in post-call memory. -/
theorem lst_new_stable_post_source_array (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    ∃ w : BitVec 64, v = .val (.word w) ∧
      Disj (memW post w.toNat, 8 * locN s "stable_log_cap")
        (memW post (locN s "logs"), 8 * memW post (locN s "logs" + 8)) := by
  obtain ⟨w, hv, hs⟩ := lst_new_stable_source_separation h s vs body callee ret v post hc hp ha hl hr
  obtain ⟨hptr, hlen⟩ := lst_new_stable_source_cells h s vs body callee ret v post hc hp hl hr
  refine ⟨w, hv, ?_⟩
  rw [hptr, hlen]
  exact (hs _ (by simp)).2.1

/-- Restored source headers are disjoint from the fresh stable backing. -/
theorem lst_new_stable_resumed_source_header (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    let t := setVarHOLFinite (ofString "stable_logs") v {post with locals := s.locals}
    Disj (locN t "logs", 24)
      (memW t (locN t "stable_logs"), 8 * locN t "stable_log_cap") := by
  obtain ⟨w, rfl, hs⟩ :=
    lst_new_stable_source_separation h s vs body callee ret v post hc hp ha hl hr
  have hd := (hs (memW post w.toNat, 8 * locN s "stable_log_cap") (by simp)).1
  simpa [locN, memW, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
    show ofString "stable_logs" ≠ ofString "logs" by decide,
    show ofString "stable_logs" ≠ ofString "stable_log_cap" by decide] using
    R13Shards.disj_symm hd

/-- The resumed source array is disjoint from the fresh stable backing. -/
theorem lst_new_stable_resumed_source_array (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    let t := setVarHOLFinite (ofString "stable_logs") v {post with locals := s.locals}
    Disj (memW t (locN t "logs"), 8 * memW t (locN t "logs" + 8))
      (memW t (locN t "stable_logs"), 8 * locN t "stable_log_cap") := by
  obtain ⟨w, rfl, hd⟩ :=
    lst_new_stable_post_source_array h s vs body callee ret v post hc hp ha hl hr
  simpa [locN, memW, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
    show ofString "stable_logs" ≠ ofString "logs" by decide,
    show ofString "stable_logs" ≠ ofString "stable_log_cap" by decide] using
    R13Shards.disj_symm hd

/-- Fresh stable headers remain separate from the source header and backing
when source addresses are read in the returned memory. -/
theorem lst_new_stable_post_header_separation (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    ∃ w : BitVec 64, v = .val (.word w) ∧
      Disj (locN s "logs", 24) (w.toNat, 24) ∧
      Disj (memW post (locN s "logs"), 8 * memW post (locN s "logs" + 8))
        (w.toNat, 24) := by
  obtain ⟨w, hv, hs⟩ := lst_new_stable_source_separation h s vs body callee ret v post hc hp ha hl hr
  obtain ⟨hptr, hlen⟩ := lst_new_stable_source_cells h s vs body callee ret v post hc hp hl hr
  have hd := hs (w.toNat, 24) (by simp)
  refine ⟨w, hv, R13Shards.disj_symm hd.1, ?_⟩
  rw [hptr, hlen]
  exact R13Shards.disj_symm hd.2.1

/-- Express header/source separation with the caller locals restored. -/
theorem lst_new_stable_resumed_header_separation (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    let t := setVarHOLFinite (ofString "stable_logs") v {post with locals := s.locals}
    Disj (locN t "logs", 24) (locN t "stable_logs", 24) ∧
      Disj (memW t (locN t "logs"), 8 * memW t (locN t "logs" + 8))
        (locN t "stable_logs", 24) := by
  obtain ⟨w, rfl, hh, hb⟩ :=
    lst_new_stable_post_header_separation h s vs body callee ret v post hc hp ha hl hr
  simpa [locN, memW, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
    show ofString "stable_logs" ≠ ofString "logs" by decide] using And.intro hh hb

/-- Source-record separation remains valid after allocator memory updates. -/
theorem lst_new_stable_post_record_separation (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    ∃ w : BitVec 64, v = .val (.word w) ∧
      ∀ i, i < memW post (locN s "logs" + 8) →
        Disj (memW post (memW post (locN s "logs") + 8 * i), 40) (w.toNat, 24) := by
  obtain ⟨w, hv, hs⟩ := lst_new_stable_source_separation h s vs body callee ret v post hc hp ha hl hr
  obtain ⟨hptr, hlen⟩ := lst_new_stable_source_cells h s vs body callee ret v post hc hp hl hr
  have he := lst_new_stable_source_entries h s vs body callee ret v post hc hp hl hr
  refine ⟨w, hv, ?_⟩
  intro i hi
  rw [hlen] at hi
  rw [hptr, he i hi]
  exact R13Shards.disj_symm ((hs _ (by simp)).2.2 i hi)

/-- Every source record remains separate from the returned backing region. -/
theorem lst_new_stable_post_backing_records (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    ∃ w : BitVec 64, v = .val (.word w) ∧
      ∀ i, i < memW post (locN s "logs" + 8) →
        Disj (memW post (memW post (locN s "logs") + 8 * i), 40)
          (memW post w.toNat, 8 * locN s "stable_log_cap") := by
  obtain ⟨w, hv, hs⟩ := lst_new_stable_source_separation h s vs body callee ret v post hc hp ha hl hr
  obtain ⟨hptr, hlen⟩ := lst_new_stable_source_cells h s vs body callee ret v post hc hp hl hr
  have he := lst_new_stable_source_entries h s vs body callee ret v post hc hp hl hr
  refine ⟨w, hv, ?_⟩
  intro i hi
  rw [hlen] at hi
  rw [hptr, he i hi]
  exact R13Shards.disj_symm ((hs _ (by simp)).2.2 i hi)

/-- Restore the source-record/backing separation needed by copy setup. -/
theorem lst_new_stable_resumed_backing_records (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    let t := setVarHOLFinite (ofString "stable_logs") v {post with locals := s.locals}
    ∀ i, i < memW t (locN t "logs" + 8) →
      Disj (memW t (memW t (locN t "logs") + 8 * i), 40)
        (memW t (locN t "stable_logs"), 8 * locN t "stable_log_cap") := by
  obtain ⟨w, rfl, he⟩ :=
    lst_new_stable_post_backing_records h s vs body callee ret v post hc hp ha hl hr
  simpa [locN, memW, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
    show ofString "stable_logs" ≠ ofString "logs" by decide,
    show ofString "stable_logs" ≠ ofString "stable_log_cap" by decide] using he

/-- Restore caller locals in the source-record separation conclusion. -/
theorem lst_new_stable_resumed_record_separation (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    let t := setVarHOLFinite (ofString "stable_logs") v {post with locals := s.locals}
    ∀ i, i < memW t (locN t "logs" + 8) →
      Disj (memW t (memW t (locN t "logs") + 8 * i), 40) (locN t "stable_logs", 24) := by
  obtain ⟨w, rfl, he⟩ :=
    lst_new_stable_post_record_separation h s vs body callee ret v post hc hp ha hl hr
  simpa [locN, memW, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
    show ofString "stable_logs" ≠ ofString "logs" by decide] using he

/-- Source ownership and fresh-header separation share allocator witnesses. -/
theorem lst_new_stable_joint_owned (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    ∃ w : BitVec 64, v = .val (.word w) ∧ ∃ S Nd,
      WorldTypedWith post S Nd ∧ LogsLiveOwned post S Nd (locN s "logs") ∧
      ∀ o ∈ worldOwned post S Nd, Disj (w.toNat, 24) o := by
  have hw := funSpec_at_lookup h.wk_lst_new s hc vs body callee ret hl
    (worldOK_callEntry hp.1.1.1.1.1.1 callee) (by rw [hr]; simp)
  rw [hr] at hw
  obtain ⟨a, b, _, _, _, _, ho⟩ := hp.1.1.1.2.2.2
  have hLc := (R13Shards.logsListOK_with_locals s callee (s.clock - 1) _).mpr hp.1.1.1.2.1
  have hOc := logsWorldOwned_with_locals callee (s.clock - 1) ho
  obtain ⟨S, Nd, hW, hO, hQ⟩ := logsWorldOwned_heapStep_joint
    (hw (Or.inl ⟨v, rfl⟩)) (worldOK_callEntry hp.1.1.1.1.1.1 callee).1 hLc hOc
  have hargs := lst_new_stable_args s vs body callee ret hc hp ha hl
  obtain ⟨w, hv, hd⟩ := hQ hargs.2.2.2 v rfl
  exact ⟨w, hv, S, Nd, hW, hO, fun o ho => hd _ (by simp) o ho⟩

/-- The same allocator world witnesses separate both returned regions. -/
theorem lst_new_stable_joint_regions (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    ∃ w : BitVec 64, v = .val (.word w) ∧ ∃ S Nd,
      WorldTypedWith post S Nd ∧ LogsLiveOwned post S Nd (locN s "logs") ∧
      (∀ o ∈ worldOwned post S Nd, Disj (w.toNat, 24) o) ∧
      (∀ o ∈ worldOwned post S Nd,
        Disj (memW post w.toNat, 8 * locN s "stable_log_cap") o) := by
  have hw := funSpec_at_lookup h.wk_lst_new s hc vs body callee ret hl
    (worldOK_callEntry hp.1.1.1.1.1.1 callee) (by rw [hr]; simp)
  rw [hr] at hw
  obtain ⟨a, b, _, _, _, _, ho⟩ := hp.1.1.1.2.2.2
  have hLc := (R13Shards.logsListOK_with_locals s callee (s.clock - 1) _).mpr hp.1.1.1.2.1
  have hOc := logsWorldOwned_with_locals callee (s.clock - 1) ho
  obtain ⟨S, Nd, hW, hO, hQ⟩ := logsWorldOwned_heapStep_joint
    (hw (Or.inl ⟨v, rfl⟩)) (worldOK_callEntry hp.1.1.1.1.1.1 callee).1 hLc hOc
  have hargs := lst_new_stable_args s vs body callee ret hc hp ha hl
  obtain ⟨w, hv, hd⟩ := hQ hargs.2.2.2 v rfl
  refine ⟨w, hv, S, Nd, hW, hO, fun o ho => hd _ (by simp) o ho, ?_⟩
  intro o ho
  have hb := hd (memW post w.toNat,
    locN (callEntryStateHOLFinite s callee) "esz" *
      locN (callEntryStateHOLFinite s callee) "cap") (by simp) o ho
  simpa only [hargs.1, hargs.2.1] using hb

/-- Restoring caller locals retains the joint separation witnesses for both
regions used by the stable copy. -/
theorem lst_new_stable_resumed_joint_regions (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    let t := setVarHOLFinite (ofString "stable_logs") v {post with locals := s.locals}
    ∃ S Nd, WorldTypedWith t S Nd ∧ LogsLiveOwned t S Nd (locN t "logs") ∧
      (∀ o ∈ worldOwned t S Nd, Disj (locN t "stable_logs", 24) o) ∧
      (∀ o ∈ worldOwned t S Nd,
        Disj (memW t (locN t "stable_logs"), 8 * locN t "stable_log_cap") o) := by
  obtain ⟨w, rfl, S, Nd, hW, hO, hh, hb⟩ :=
    lst_new_stable_joint_regions h s vs body callee ret v post hc hp ha hl hr
  refine ⟨S, Nd, ?_, ?_, ?_, ?_⟩
  · exact (R13Shards.worldTypedWith_with_locals post _ post.clock S Nd).mpr hW
  · change LogsLiveOwned post S Nd _
    simpa [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "stable_logs" ≠ ofString "logs" by decide] using hO
  · change ∀ o ∈ worldOwned post S Nd, Disj _ o
    simpa [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE] using hh
  · change ∀ o ∈ worldOwned post S Nd, Disj _ o
    simpa [locN, memW, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "stable_logs" ≠ ofString "stable_log_cap" by decide] using hb

/-- Assemble all copy spatial facts directly from the allocation return. -/
theorem lst_new_stable_resumed_spatial (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    StableCopySpatial
      (setVarHOLFinite (ofString "stable_logs") v {post with locals := s.locals}) := by
  obtain ⟨S, Nd, hW, hO, _, hb⟩ :=
    lst_new_stable_resumed_joint_regions h s vs body callee ret v post hc hp ha hl hr
  exact ⟨S, Nd, hW, hO, hb,
    lst_new_stable_resumed_source_header h s vs body callee ret v post hc hp ha hl hr,
    lst_new_stable_resumed_header_backing h s vs body callee ret v post hc hp ha hl hr,
    lst_new_stable_resumed_source_array h s vs body callee ret v post hc hp ha hl hr,
    lst_new_stable_resumed_backing_records h s vs body callee ret v post hc hp ha hl hr⟩

/-- Allocation establishes the full precondition for the stable length write,
given the caller's word-shaped length operand. -/
theorem lst_new_stable_length_pre (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (hn : s.locals.lookup (ofString "nl") =
      some (.val (.word (BitVec.ofNat 64 (locN s "nl")))))
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    StableLengthPre (setVarHOLFinite (ofString "stable_logs") v {post with locals := s.locals}) := by
  obtain ⟨hstorage, halloc, hword, hnword⟩ :=
    lst_new_stable_length_operands h s vs body callee ret v post hc hp hn ha hl hr
  obtain ⟨hh, hb⟩ := lst_new_stable_resumed_header_separation h s vs body callee ret v post hc hp ha hl hr
  have he := lst_new_stable_resumed_record_separation h s vs body callee ret v post hc hp ha hl hr
  obtain ⟨w, rfl, S, Nd, hW, hO, hdisj⟩ := lst_new_stable_joint_owned h s vs body callee ret v post hc hp ha hl hr
  refine ⟨hstorage, halloc, hword, hnword, S, Nd, ?_, ?_, ?_, hh, hb, he⟩
  · exact (R13Shards.worldTypedWith_with_locals post _ post.clock S Nd).mpr hW
  · change LogsLiveOwned post S Nd _
    simpa [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "stable_logs" ≠ ofString "logs" by decide] using hO
  · change ∀ o ∈ worldOwned post S Nd, Disj _ o
    simpa [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE] using hdisj

/-- Restoring caller locals after allocation preserves the typed source pointer. -/
theorem stable_allocation_source_operand {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64) (p : BitVec 64)
    (hp : s.locals.lookup (ofString "lp") = some (.val (.word p))) :
    (setVarHOLFinite (ofString "stable_logs") v {post with locals := s.locals}).locals.lookup
      (ofString "lp") = some (.val (.word p)) := by
  simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
    show ofString "stable_logs" ≠ ofString "lp" by decide] using hp

/-- Allocation supplies length validity and copy separation in the same resumed state. -/
theorem lst_new_stable_length_spatial (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (hn : s.locals.lookup (ofString "nl") =
      some (.val (.word (BitVec.ofNat 64 (locN s "nl")))))
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    let t := setVarHOLFinite (ofString "stable_logs") v {post with locals := s.locals}
    StableLengthPre t ∧ StableCopySpatial t := by
  exact ⟨lst_new_stable_length_pre h s vs body callee ret v post hc hp hn ha hl hr,
    lst_new_stable_resumed_spatial h s vs body callee ret v post hc hp ha hl hr⟩

/-- Allocation supplies the coherent spatial precondition of the length write. -/
theorem lst_new_stable_length_joint_pre (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (hn : s.locals.lookup (ofString "nl") =
      some (.val (.word (BitVec.ofNat 64 (locN s "nl")))))
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    let t := setVarHOLFinite (ofString "stable_logs") v {post with locals := s.locals}
    StableLengthPre t ∧
      (∃ S Nd, WorldTypedWith t S Nd ∧ LogsLiveOwned t S Nd (locN t "logs") ∧
        (∀ o ∈ worldOwned t S Nd, Disj (locN t "stable_logs", 24) o) ∧
        (∀ o ∈ worldOwned t S Nd,
          Disj (memW t (locN t "stable_logs"), 8 * locN t "stable_log_cap") o)) ∧
      Disj (locN t "logs", 24)
        (memW t (locN t "stable_logs"), 8 * locN t "stable_log_cap") ∧
      Disj (locN t "stable_logs", 24)
        (memW t (locN t "stable_logs"), 8 * locN t "stable_log_cap") ∧
      Disj (memW t (locN t "logs"), 8 * memW t (locN t "logs" + 8))
        (memW t (locN t "stable_logs"), 8 * locN t "stable_log_cap") ∧
      ∀ j, j < memW t (locN t "logs" + 8) →
        Disj (memW t (memW t (locN t "logs") + 8 * j), 40)
          (memW t (locN t "stable_logs"), 8 * locN t "stable_log_cap") := by
  exact ⟨lst_new_stable_length_pre h s vs body callee ret v post hc hp hn ha hl hr,
    lst_new_stable_resumed_joint_regions h s vs body callee ret v post hc hp ha hl hr,
    lst_new_stable_resumed_source_header h s vs body callee ret v post hc hp ha hl hr,
    lst_new_stable_resumed_header_backing h s vs body callee ret v post hc hp ha hl hr,
    lst_new_stable_resumed_source_array h s vs body callee ret v post hc hp ha hl hr,
    lst_new_stable_resumed_backing_records h s vs body callee ret v post hc hp ha hl hr⟩

/-- Returning from allocation retains the remaining non-spatial copy operands. -/
theorem lst_new_stable_copy_operands (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (hz : locN s "logs" ≠ 0)
    (hptr : ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p)))
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    let t := setVarHOLFinite (ofString "stable_logs") v {post with locals := s.locals}
    locN t "logs" ≠ 0 ∧ WordsOK t (locN t "stable_logs", 24) ∧
      ∃ p : BitVec 64, t.locals.lookup (ofString "lp") = some (.val (.word p)) := by
  refine ⟨?_, (lst_new_stable_header_resume h s vs body callee ret v post hc hp ha hl hr).1, ?_⟩
  · simpa [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "stable_logs" ≠ ofString "logs" by decide] using hz
  · simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "stable_logs" ≠ ofString "lp" by decide] using hptr

/-- A typed length operand has its canonical representation even at zero. -/
theorem stable_length_canonical_operand {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hn : ∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) :
    s.locals.lookup (ofString "nl") =
      some (.val (.word (BitVec.ofNat 64 (locN s "nl")))) := by
  obtain ⟨n, hn⟩ := hn
  simpa [locN, hn] using hn

/-- The allocator's return state enters the bounded length/copy suffix and receipt tail. -/
theorem lst_new_stable_copy_continuation (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (hn : s.locals.lookup (ofString "nl") =
      some (.val (.word (BitVec.ofNat 64 (locN s "nl")))))
    (hz : locN s "logs" ≠ 0)
    (hptr : ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p)))
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post))
    (hcode : post.code = originalRuntimeCode)
    {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn PtxReceiptsDone tail b) :
    TerminatingRunBounded
      (setVarHOLFinite (ofString "stable_logs") v {post with locals := s.locals})
      (.seq (.store (.op .add [.var .local (ofString "stable_logs"), .const 8])
        (.var .local (ofString "nl")))
        (.seq (.assign .local (ofString "stable_lp")
          (.load .one (.var .local (ofString "stable_logs"))))
          (.seq (.assign .local (ofString "i") (.const 0))
            (.seq (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl")))
              (.seq (.store (.op .add [.var .local (ofString "stable_lp"),
                .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
                (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))))
              tail)))) (2 ^ 28 + 1 + b) := by
  exact stable_length_setup_loop_cut htail _ hcode
    ⟨lst_new_stable_length_joint_pre h s vs body callee ret v post hc hp hn ha hl hr,
      lst_new_stable_copy_operands h s vs body callee ret v post hc hp hz hptr ha hl hr⟩

/-- Execute the stable length write using the allocation's joint spatial witnesses. -/
theorem lst_new_stable_length_write (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post u : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (hn : ∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n)))
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post))
    (hcode : post.code = originalRuntimeCode)
    (he : evaluateHOLFiniteState
      (setVarHOLFinite (ofString "stable_logs") v {post with locals := s.locals})
      (.store (.op .add [.var .local (ofString "stable_logs"), .const 8])
        (.var .local (ofString "nl"))) = (none, u)) :
    StableLengthPost u ∧ StableCopySpatial u := by
  have hpre := lst_new_stable_length_joint_pre h s vs body callee ret v post hc hp
    (stable_length_canonical_operand s hn) ha hl hr
  have hout := hoare_stable_length_joint.run
    (setVarHOLFinite (ofString "stable_logs") v {post with locals := s.locals}) hcode hpre
    (by rw [he]; simp)
  rw [he] at hout
  exact hout rfl

/-- The concrete allocation call preserves the complete spatial and operand package. -/
theorem hoare_lst_new_stable_copy (h : PtxCallees) :
    Hoare (fun s => Phase4StableCapReady s ∧
      (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
      locN s "logs" ≠ 0 ∧
      ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p)))
      (.call (some (some (VarKind.local, ofString "stable_logs"), none)) (ofString "lst_new")
        [.const 8, .var .local (ofString "stable_log_cap")])
      (fun r t => r = none → StableLengthPre t ∧ StableCopySpatial t ∧
        locN t "logs" ≠ 0 ∧ WordsOK t (locN t "stable_logs", 24) ∧
        ∃ p : BitVec 64, t.locals.lookup (ofString "lp") = some (.val (.word p))) := by
  apply Hoare.callLocal_resume
  intro F s vs body callee ret v post hc hp ha hl hr
  obtain ⟨hpre, hs⟩ := lst_new_stable_length_spatial h s vs body callee ret v post hc hp.1
    (stable_length_canonical_operand s hp.2.1) ha hl hr
  exact ⟨hpre, hs,
    lst_new_stable_copy_operands h s vs body callee ret v post hc hp.1 hp.2.2.1 hp.2.2.2 ha hl hr⟩

/-- Retain the coherent header/world witness needed by the subsequent length store. -/
theorem hoare_lst_new_stable_joint (h : PtxCallees) :
    Hoare (fun s => Phase4StableCapReady s ∧
      (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
      locN s "logs" ≠ 0 ∧
      ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p)))
      (.call (some (some (.local, ofString "stable_logs"), none)) (ofString "lst_new")
        [.const 8, .var .local (ofString "stable_log_cap")])
      (fun r s => r = none → (StableLengthPre s ∧
        (∃ S Nd, WorldTypedWith s S Nd ∧ LogsLiveOwned s S Nd (locN s "logs") ∧
          (∀ o ∈ worldOwned s S Nd, Disj (locN s "stable_logs", 24) o) ∧
          (∀ o ∈ worldOwned s S Nd,
            Disj (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") o)) ∧
        Disj (locN s "logs", 24)
          (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
        Disj (locN s "stable_logs", 24)
          (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
        Disj (memW s (locN s "logs"), 8 * memW s (locN s "logs" + 8))
          (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
        ∀ j, j < memW s (locN s "logs" + 8) →
          Disj (memW s (memW s (locN s "logs") + 8 * j), 40)
            (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap")) ∧
        locN s "logs" ≠ 0 ∧ WordsOK s (locN s "stable_logs", 24) ∧
        ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p))) := by
  apply Hoare.callLocal_resume
  intro F s vs body callee ret v post hc hp ha hl hr
  exact ⟨lst_new_stable_length_joint_pre h s vs body callee ret v post hc hp.1
      (stable_length_canonical_operand s hp.2.1) ha hl hr,
    lst_new_stable_copy_operands h s vs body callee ret v post hc hp.1 hp.2.2.1 hp.2.2.2 ha hl hr⟩

/-- Scoped allocation followed by the concrete stable-copy suffix. -/
theorem stable_allocation_decl_loop_cut (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn PtxReceiptsDone tail b) :
    TerminatingProgBoundedOn (fun s => Phase4StableCapReady s ∧
      (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
      locN s "logs" ≠ 0 ∧
      ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p)))
      (spinePlug 5 (spineAt 132 ptxCode) tail)
      (K.lst_new + (2 ^ 28 + 1 + b) + 1) := by
  have he : spinePlug 5 (spineAt 132 ptxCode) tail =
      .decCall (ofString "stable_logs") .one (ofString "lst_new")
        [.const 8, .var .local (ofString "stable_log_cap")]
        (spinePlug 4 (spineAt 133 ptxCode) tail) := by
    unfold ptxCode
    rfl
  rw [he]
  intro F s hc hp
  refine TerminatingProgBoundedOn.decCall_on
    (P := fun s => Phase4StableCapReady s ∧
      (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
      locN s "logs" ≠ 0 ∧
      ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p)))
    h.fb_lst_new _ _ _ ?_ ?_ (stable_length_decl_loop_cut htail) s hc hp
  · intro G t vs body callee ret hc hp ha hl
    exact guestInv_callEntry t callee hp.1.1.1.1.1.1.1.1.1
  · intro G t vs body callee ret v post hc hp ha hl hr
    exact ⟨lst_new_stable_length_joint_pre h t vs body callee ret v post hc hp.1
        (stable_length_canonical_operand t hp.2.1) ha hl hr,
      lst_new_stable_copy_operands h t vs body callee ret v post hc hp.1 hp.2.2.1 hp.2.2.2 ha hl hr⟩

/-- Allocation enters the owned length/copy suffix with its joint witnesses. -/
theorem stable_allocation_decl_loop_owned_cut (h : PtxCallees)
    {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn
      (fun s => PtxReceiptsDone s ∧ LogsWorldOwned s (locN s "stable_logs") ∧
        locN s "stable_logs" ≠ 0 ∧
        ∃ w : BitVec 64, s.locals.lookup (ofString "stable_logs") = some (.val (.word w))) tail b) :
    TerminatingProgBoundedOn (fun s => Phase4StableCapReady s ∧
      (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
      locN s "logs" ≠ 0 ∧
      ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p)))
      (spinePlug 5 (spineAt 132 ptxCode) tail)
      (K.lst_new + (2 ^ 28 + 1 + b) + 1) := by
  have he : spinePlug 5 (spineAt 132 ptxCode) tail =
      .decCall (ofString "stable_logs") .one (ofString "lst_new")
        [.const 8, .var .local (ofString "stable_log_cap")]
        (spinePlug 4 (spineAt 133 ptxCode) tail) := by
    unfold ptxCode
    rfl
  rw [he]
  intro F s hc hp
  refine TerminatingProgBoundedOn.decCall_on
    (P := fun s => Phase4StableCapReady s ∧
      (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
      locN s "logs" ≠ 0 ∧
      ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p)))
    h.fb_lst_new _ _ _ ?_ ?_ (stable_length_decl_loop_owned_cut htail) s hc hp
  · intro G t vs body callee ret hc hp ha hl
    exact guestInv_callEntry t callee hp.1.1.1.1.1.1.1.1.1
  · intro G t vs body callee ret v post hc hp ha hl hr
    exact ⟨lst_new_stable_length_joint_pre h t vs body callee ret v post hc hp.1
        (stable_length_canonical_operand t hp.2.1) ha hl hr,
      lst_new_stable_copy_operands h t vs body callee ret v post hc hp.1 hp.2.2.1 hp.2.2.2 ha hl hr⟩

/-- A world-owned slot write preserves a separately owned stable receipt list. -/
theorem ptxReceiptsDone_worldStore {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxReceiptsDone s) (hn : locN s "stable_logs" ≠ 0)
    {S Nd : List Nat} (hW : WorldTypedWith s S Nd)
    (hown : LogsLiveOwned s S Nd (locN s "stable_logs"))
    {x : BitVec 64} {mem' : BitVec 64 → HolWordLab 64}
    (hm : ∀ a, a ≠ x → mem' a = s.memory a)
    (hwrite : ∃ o ∈ worldOwned s S Nd, Inside (x.toNat, 8) o.1 (o.1 + o.2))
    (hpost : TxWorld {s with memory := mem'})
    (heq : worldOwned {s with memory := mem'} S Nd = worldOwned s S Nd) :
    PtxReceiptsDone {s with memory := mem'} := by
  have hl := logsLiveOwned_single_store hp.1.1.1.2 hp.1.1.1.1 hpost.1.1.1
    hp.2.1 hown hm hwrite heq
  obtain ⟨o, ho, hin⟩ := hwrite
  have hu : IvlUnhit s {s with memory := mem'} (locN s "stable_logs", 24) :=
    ivlUnhit_single hm (by simp)
      (disj_of_inside_right hin ((hown hn).2.1 _ (by simp) o ho))
  have hh := hp.2.1.resolve_left hn
  have h8 := memW_eq_of_ivlUnhit (a := locN s "stable_logs" + 8) hu
    (by have := hh.1.1; omega) (ivl_allocated_bound hp.1.1.1.2 hh.2.1).2
    ⟨by omega, by omega⟩
  refine ⟨hpost, hl.1, ?_⟩
  change memW {s with memory := mem'} (locN s "stable_logs" + 8) < 2 ^ 28
  rw [h8]
  exact hp.2.2

/-- Specialize stable receipt preservation to the block receipt-log array. -/
theorem ptxReceiptsDone_store_bo72 {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxReceiptsDone s) (hn : locN s "stable_logs" ≠ 0)
    {S Nd : List Nat} (hW : WorldTypedWith s S Nd)
    (hown : LogsLiveOwned s S Nd (locN s "stable_logs"))
    (hback : memW s (memW s (globN s "bo" + 72)) ≠ 0)
    {x : BitVec 64} (hx : s.memaddrs x)
    (hin : Inside (x.toNat, 8) (memW s (memW s (globN s "bo" + 72)))
      (memW s (memW s (globN s "bo" + 72)) +
        8 * memW s (memW s (globN s "bo" + 72) + 16)))
    {mem' : BitVec 64 → HolWordLab 64} (hm : ∀ a, a ≠ x → mem' a = s.memory a) :
    PtxReceiptsDone {s with memory := mem'} := by
  obtain ⟨hWT, heq, henv⟩ := store_bo_array_world hp.1.1.1 hp.1.2 hW
    (Or.inr (Or.inr ⟨rfl, hback, rfl⟩)) hx hin hm
  have hg : GuestInv {s with memory := mem'} :=
    guestInv_congr (s := s) rfl rfl rfl rfl hp.1.1.1.1
  apply ptxReceiptsDone_worldStore hp hn hW hown hm ?_
    ⟨worldOK_of_parts ⟨hg, hp.1.1.1.2⟩ hWT, henv⟩ heq
  obtain ⟨_, _, hbo⟩ := blockOutObjects_eq_list hp.1.2 hW.1
  let arr := (memW s (memW s (globN s "bo" + 72)),
    8 * memW s (memW s (globN s "bo" + 72) + 16))
  have hmemb : arr ∈ blockOutObjects s := by
    rw [hbo]
    simp [arr, hback, hp.1.2.bo_nz,
      show memW s (memW s (globN s "bo" + 72) + 16) ≠ 0 from by omega]
  have hmemf : arr ∈ fixedObjects s := List.mem_append_left _ (List.mem_append_right _ hmemb)
  refine ⟨arr, ?_, hin⟩
  unfold worldOwned
  simp only [List.mem_append]
  exact Or.inl (Or.inr hmemf)

/-- A heap-only world step preserves an owned non-null stable receipt list. -/
theorem ptxReceiptsDone_heapStep {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {r : Option (PanSemResultExact 64)}
    (hs : WorldStep (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])] Q s r post)
    (hp : PtxReceiptsDone s) (ho : LogsWorldOwned s (locN s "stable_logs"))
    (hn : locN s "stable_logs" ≠ 0) :
    PtxReceiptsDone {post with locals := s.locals} ∧
      LogsWorldOwned {post with locals := s.locals} (locN s "stable_logs") := by
  have hgrow : AllocatorGrows s post := ⟨hs.2.1, by
    have he : globN post "scratch_ptr" = globN s "scratch_ptr" :=
      R16Shards.globN_eq_of_lookup (hs.2.2.1 _ (by decide))
    omega⟩
  have hlogs := logsWorldOwned_scratchStep hs hp.1.1.1 hgrow hp.2.1 ho
    (gs := []) (by intro e he; cases he) rfl (by decide)
  have hh := logsWorldOwned_heapStep_header hs hp.1.1.1 hp.2.1 ho hn
  obtain ⟨S, Nd, hw, _⟩ := ho
  have henv := txEnv_preserved_by_worldStep hs (by decide) (by decide)
    (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (by simp)
    (by intro k hk; simp only [List.mem_cons, List.not_mem_nil, or_false] at hk ⊢
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> simp)
    (by intro i hi; cases hi) (bo_words hw.2.2.1 hp.1.2.bo_nz).2.1
    (by intro i hi; cases hi) hp.1.2 (locals := s.locals) rfl
  have hown := logsWorldOwned_with_locals s.locals post.clock hlogs.2
  refine ⟨⟨⟨worldOK_of_parts
    ((arenaReady_with_locals post s.locals post.clock).mpr hs.1)
    hown.choose_spec.choose_spec.1, henv⟩, ?_, ?_⟩, hown⟩
  · exact (R13Shards.logsListOK_with_locals post s.locals post.clock _).mpr hlogs.1
  · change memW post (locN s "stable_logs" + 8) < 2 ^ 28
    rw [hh.2]
    exact hp.2.2

/-- The final receipt push selects the block's receipt-log list. -/
theorem lst_push_bo72_arg {F : Type} (s : PanSemStateFiniteExact 64 F)
    (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (hc : s.code = originalRuntimeCode) (hp : TxWorld s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.load .one (.op .add [.var .global (ofString "bo"), .const 72]), .const 8] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_push") vs = some (body, callee, ret)) :
    BoListArg (callEntryStateHOLFinite s callee) ∧
      locN (callEntryStateHOLFinite s callee) "l" = memW s (globN s "bo" + 72) := by
  have ha' := ha
  rw [evalListHOLFinite_eq_toExact] at ha'
  rcases hload : evalAt s (.load .one (.op .add [.var .global (ofString "bo"), .const 72])) with _ | vl
  · simp only [evalListHOLExact, hload] at ha'; cases ha'
  obtain ⟨w, rfl, hw⟩ := evalAt_loadG s "bo" 72 vl hload
  have hparams := callee_param_two_exp s (ofString "lst_push") (ofString "l") (ofString "esz")
    .one .one _ _ (by rw [hc]; exact lookup_lst_push)
    (.load .one (.op .add [.var .global (ofString "bo"), .const 72])) (.const 8)
    (.val (.word w)) (.val (.word 8)) vs body callee ret hload rfl ha hl
  have hle : locN (callEntryStateHOLFinite s callee) "l" = memW s (globN s "bo" + 72) := by
    simpa only [locN, callEntryStateHOLFinite, hparams.2.1,
      show (72 : BitVec 64).toNat = 72 from rfl] using hw
  refine ⟨⟨worldOK_callEntry hp.1 callee, hp.2.bo_nz, Or.inr hle, ?_⟩, hle⟩
  simp only [locN, callEntryStateHOLFinite, hparams.2.2]
  rfl

/-- The receipt-list push uses the second component of the backing invariant. -/
theorem lst_push_bo72_arg_backing {F : Type} (s : PanSemStateFiniteExact 64 F)
    (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (hc : s.code = originalRuntimeCode) (hp : TxWorld s) (hb : TxBacking s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.load .one (.op .add [.var .global (ofString "bo"), .const 72]), .const 8] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_push") vs = some (body, callee, ret)) :
    BoListArgStrong (callEntryStateHOLFinite s callee) := by
  obtain ⟨harg, he⟩ := lst_push_bo72_arg s vs body callee ret hc hp ha hl
  refine ⟨harg.1, harg, ?_⟩
  rw [he]
  exact hb.2

/-- The final push returns a slot in the current receipt-log backing array. -/
theorem lst_push_bo72_slot_result (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : TxWorld s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.load .one (.op .add [.var .global (ofString "bo"), .const 72]), .const 8] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_push") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat % 8 = 0 ∧
      Inside (w.toNat, 8) (memW post (memW post (globN post "bo" + 72)))
        (memW post (memW post (globN post "bo" + 72)) +
          8 * memW post (memW post (globN post "bo" + 72) + 16)) := by
  have harg := lst_push_bo72_arg s vs body callee ret hc hp ha hl
  have hw := funSpec_at_lookup h.wk_lst_push s hc vs body callee ret hl harg.1 (by rw [hr]; simp)
  rw [hr] at hw
  have hs := hw (Or.inl ⟨v, rfl⟩)
  have hbo : globN post "bo" = globN s "bo" :=
    R16Shards.globN_eq_of_lookup (hs.2.2.1 _ (by decide))
  have hm : memW post (globN s "bo" + 72) = memW s (globN s "bo" + 72) :=
    hs.2.2.2.1 ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])
      (by simp) hp.2.bo_nz 72 (by simp) (by intro i hi; cases hi)
  obtain ⟨w, hv, hal, hin⟩ := lst_push_slot_result h s vs body callee ret v post hc hl hr harg.1
  refine ⟨w, hv, hal, ?_⟩
  rw [hbo, hm]
  simpa only [harg.2] using hin

/-- Spatial facts required at the final receipt slot. -/
def Phase4ReceiptSlotReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => PtxReceiptsDone s ∧ locN s "stable_logs" ≠ 0 ∧
    (∃ S Nd, WorldTypedWith s S Nd ∧ LogsLiveOwned s S Nd (locN s "stable_logs")) ∧
    memW s (memW s (globN s "bo" + 72)) ≠ 0 ∧
    Inside (locN s "rl", 8) (memW s (memW s (globN s "bo" + 72)))
      (memW s (memW s (globN s "bo" + 72)) +
        8 * memW s (memW s (globN s "bo" + 72) + 16)) ∧
    ∃ w : BitVec 64, s.locals.lookup (ofString "stable_logs") = some (.val (.word w))

/-- Storing the stable list into the returned receipt slot preserves the cut. -/
theorem hoare_receiptSlot_store :
    Hoare Phase4ReceiptSlotReady
      (.store (.var .local (ofString "rl")) (.var .local (ofString "stable_logs")))
      (fun r t => r = none → PtxReceiptsDone t) := by
  refine R13Shards.Hoare.store_fall fun s x v mem' hp hx hv hst => ?_
  obtain ⟨hdone, hn, ⟨S, Nd, hW, hown⟩, hback, hin, w, hw⟩ := hp
  have hv' : v = .val (.word w) := by
    simpa [evalAt, evalHOLExact, hw] using hv.symm
  subst v
  obtain ⟨hdom, _, hmem⟩ := R13Shards.panMemStoresHOL_word_spec
    (by simpa only [flattenHOL] using hst)
  have hrl : locN s "rl" = x.toNat := by
    have hlu : s.locals.lookup (ofString "rl") = some (.val (.word x)) := hx
    simp only [locN, hlu]
  apply ptxReceiptsDone_store_bo72 hdone hn hW hown hback hdom _ hmem
  simpa only [hrl] using hin

/-- Restoring the receipt-slot local preserves the stable receipt cut. -/
theorem ptxReceiptsDone_set_rl {F : Type} (s : PanSemStateFiniteExact 64 F)
    (v : ValueHOL 64) (hp : PtxReceiptsDone s) :
    PtxReceiptsDone (setVarHOLFinite (ofString "rl") v s) := by
  have ht : TxWorld (setVarHOLFinite (ofString "rl") v s) :=
    LocalsOnly.setVar localsOnly_txWorld (by decide) v s hp.1
  have he : locN (setVarHOLFinite (ofString "rl") v s) "stable_logs" =
      locN s "stable_logs" := by
    simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "rl" ≠ ofString "stable_logs" by decide]
  refine ⟨ht, ?_, ?_⟩
  · rw [he]
    exact (R13Shards.logsListOK_with_locals s _ s.clock _).mpr hp.2.1
  · change memW s (locN (setVarHOLFinite (ofString "rl") v s) "stable_logs" + 8) < 2 ^ 28
    rw [he]
    exact hp.2.2

/-- The receipt push retains the owned stable list and returns a writable slot. -/
theorem resume_lst_push_owned_receiptSlot (h : PtxCallees)
    (hnonzero : LstPushBackingNonzero) :
    DecCallResumeOn (fun s => PtxReceiptsDone s ∧
      LogsWorldOwned s (locN s "stable_logs") ∧ locN s "stable_logs" ≠ 0 ∧
      ∃ w : BitVec 64, s.locals.lookup (ofString "stable_logs") = some (.val (.word w)))
      Phase4ReceiptSlotReady (ofString "rl") (ofString "lst_push")
      [.load .one (.op .add [.var .global (ofString "bo"), .const 72]), .const 8] := by
  intro F s vs body callee ret v post hc hp ha hl hr
  have harg := lst_push_bo72_arg s vs body callee ret hc hp.1.1 ha hl
  have hw := funSpec_at_lookup h.wk_lst_push s hc vs body callee ret hl harg.1
    (by rw [hr]; simp)
  rw [hr] at hw
  have hs := hw (Or.inl ⟨v, rfl⟩)
  have hs' := R13Shards.worldStep_with_locals hs s.locals s.clock
  obtain ⟨hdone, hown⟩ := ptxReceiptsDone_heapStep hs' hp.1 hp.2.1 hp.2.2.1
  have hn := funSpec_at_lookup hnonzero s hc vs body callee ret hl harg.1
    (by rw [hr]; simp)
  rw [hr] at hn
  have hbo : globN post "bo" = globN s "bo" :=
    R16Shards.globN_eq_of_lookup (hs.2.2.1 _ (by decide))
  have hm : memW post (globN s "bo" + 72) = memW s (globN s "bo" + 72) :=
    hs.2.2.2.1 ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])
      (by simp) hp.1.1.2.bo_nz 72 (by simp) (by intro i hi; cases hi)
  have hback : memW post (memW post (globN post "bo" + 72)) ≠ 0 := by
    rw [hbo, hm]
    simpa only [harg.2] using hn v rfl
  obtain ⟨q, rfl, _, hin⟩ := lst_push_bo72_slot_result h s vs body callee ret v post hc hp.1.1 ha hl hr
  have he : locN (setVarHOLFinite (ofString "rl") (.val (.word q))
      {post with locals := s.locals}) "stable_logs" = locN s "stable_logs" := by
    simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "rl" ≠ ofString "stable_logs" by decide]
  refine ⟨ptxReceiptsDone_set_rl _ _ hdone, ?_, ?_, hback, ?_, ?_⟩
  · rw [he]; exact hp.2.2.1
  · rw [he]
    exact logsWorldOwned_with_locals _ post.clock hown
  · simpa [locN, memW, globN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE] using hin
  · obtain ⟨w, hw⟩ := hp.2.2.2
    exact ⟨w, by simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "rl" ≠ ofString "stable_logs" by decide] using hw⟩

/-- The final receipt push obtains nonzero backing from the concrete strong
push theorem at a backing-aware cut. -/
theorem resume_lst_push_owned_receiptSlot_backing (h : PtxCallees) :
    DecCallResumeOn (fun s => (PtxReceiptsDone s ∧
      LogsWorldOwned s (locN s "stable_logs") ∧ locN s "stable_logs" ≠ 0 ∧
      ∃ w : BitVec 64, s.locals.lookup (ofString "stable_logs") = some (.val (.word w))) ∧
      TxBacking s) Phase4ReceiptSlotReady (ofString "rl") (ofString "lst_push")
      [.load .one (.op .add [.var .global (ofString "bo"), .const 72]), .const 8] := by
  intro F s vs body callee ret v post hc hp ha hl hr
  have harg := lst_push_bo72_arg s vs body callee ret hc hp.1.1.1 ha hl
  have hw := funSpec_at_lookup h.wk_lst_push s hc vs body callee ret hl harg.1
    (by rw [hr]; simp)
  rw [hr] at hw
  have hs := hw (Or.inl ⟨v, rfl⟩)
  have hs' := R13Shards.worldStep_with_locals hs s.locals s.clock
  obtain ⟨hdone, hown⟩ := ptxReceiptsDone_heapStep hs' hp.1.1 hp.1.2.1 hp.1.2.2.1
  have hn := funSpec_at_lookup (lst_push_backing_nonzero_strong h) s hc vs body callee ret hl
    (lst_push_bo72_arg_backing s vs body callee ret hc hp.1.1.1 hp.2 ha hl)
    (by rw [hr]; simp)
  rw [hr] at hn
  have hbo : globN post "bo" = globN s "bo" :=
    R16Shards.globN_eq_of_lookup (hs.2.2.1 _ (by decide))
  have hm : memW post (globN s "bo" + 72) = memW s (globN s "bo" + 72) :=
    hs.2.2.2.1 ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])
      (by simp) hp.1.1.1.2.bo_nz 72 (by simp) (by intro i hi; cases hi)
  have hback : memW post (memW post (globN post "bo" + 72)) ≠ 0 := by
    rw [hbo, hm]
    simpa only [harg.2] using hn v rfl
  obtain ⟨q, rfl, _, hin⟩ := lst_push_bo72_slot_result h s vs body callee ret v post hc hp.1.1.1 ha hl hr
  have he : locN (setVarHOLFinite (ofString "rl") (.val (.word q))
      {post with locals := s.locals}) "stable_logs" = locN s "stable_logs" := by
    simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "rl" ≠ ofString "stable_logs" by decide]
  refine ⟨ptxReceiptsDone_set_rl _ _ hdone, ?_, ?_, hback, ?_, ?_⟩
  · rw [he]; exact hp.1.2.2.1
  · rw [he]
    exact logsWorldOwned_with_locals _ post.clock hown
  · simpa [locN, memW, globN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE] using hin
  · obtain ⟨w, hw⟩ := hp.1.2.2.2
    exact ⟨w, by simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "rl" ≠ ofString "stable_logs" by decide] using hw⟩

/-- The final receipt-list push and slot store compose with the Phase-5 cut. -/
theorem phase4ReceiptPush_cut (h : PtxCallees)
    (R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (hresume : DecCallResumeOn PtxReceiptsDone R (ofString "rl") (ofString "lst_push")
      [.load .one (.op .add [.var .global (ofString "bo"), .const 72]), .const 8])
    (hstore : Hoare R
      (.store (.var .local (ofString "rl")) (.var .local (ofString "stable_logs")))
      (fun r t => r = none → PtxReceiptsDone t))
    {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn PtxReceiptsDone tail b) :
    TerminatingProgBoundedOn PtxReceiptsDone
      (spinePlug 2 (spineAt 137 ptxCode) tail) (K.lst_push + b + 1) := by
  have hs : TerminatingProgBoundedOn R
      (.seq (.store (.var .local (ofString "rl")) (.var .local (ofString "stable_logs"))) tail) b := by
    intro F s hc hp
    have hb := seq_bound_trans (a := 0) (fun u _ _ _ => by
      have hu := clock_store u (.var .local (ofString "rl")) (.var .local (ofString "stable_logs"))
      exact ⟨by omega, by omega⟩) hstore htail s hc hp
    simpa only [Nat.zero_add] using hb
  have he : spinePlug 2 (spineAt 137 ptxCode) tail =
      .decCall (ofString "rl") .one (ofString "lst_push")
        [.load .one (.op .add [.var .global (ofString "bo"), .const 72]), .const 8]
        (.seq (.store (.var .local (ofString "rl")) (.var .local (ofString "stable_logs"))) tail) := by
    unfold ptxCode
    rfl
  rw [he]
  intro F s hc hp
  exact TerminatingProgBoundedOn.decCall_on (P := PtxReceiptsDone)
    h.fb_lst_push _ _ _
    (fun t vs body callee ret hc hp ha hl => guestInv_callEntry t callee hp.1.1.1.1)
    hresume hs s hc hp

/-- Owned stable receipts discharge the final push and store continuation. -/
theorem phase4ReceiptPush_owned_cut (h : PtxCallees)
    (hnonzero : LstPushBackingNonzero)
    {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn PtxReceiptsDone tail b) :
    TerminatingProgBoundedOn
      (fun s => PtxReceiptsDone s ∧ LogsWorldOwned s (locN s "stable_logs") ∧
        locN s "stable_logs" ≠ 0 ∧
        ∃ w : BitVec 64, s.locals.lookup (ofString "stable_logs") = some (.val (.word w)))
      (spinePlug 2 (spineAt 137 ptxCode) tail) (K.lst_push + b + 1) := by
  have hs : TerminatingProgBoundedOn Phase4ReceiptSlotReady
      (.seq (.store (.var .local (ofString "rl")) (.var .local (ofString "stable_logs"))) tail) b := by
    intro F s hc hp
    have hb := seq_bound_trans (a := 0) (fun u _ _ _ => by
      have hu := clock_store u (.var .local (ofString "rl")) (.var .local (ofString "stable_logs"))
      exact ⟨by omega, by omega⟩) hoare_receiptSlot_store htail s hc hp
    simpa only [Nat.zero_add] using hb
  have he : spinePlug 2 (spineAt 137 ptxCode) tail =
      .decCall (ofString "rl") .one (ofString "lst_push")
        [.load .one (.op .add [.var .global (ofString "bo"), .const 72]), .const 8]
        (.seq (.store (.var .local (ofString "rl")) (.var .local (ofString "stable_logs"))) tail) := by
    unfold ptxCode
    rfl
  rw [he]
  intro F s hc hp
  exact TerminatingProgBoundedOn.decCall_on
    h.fb_lst_push _ _ _
    (fun t vs body callee ret hc hp ha hl => guestInv_callEntry t callee hp.1.1.1.1.1)
    (resume_lst_push_owned_receiptSlot h hnonzero) hs s hc hp

/-- Backing-aware receipts close the final push/store suffix without an
unguarded push-backing hypothesis. -/
theorem phase4ReceiptPush_backing_cut (h : PtxCallees)
    {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn PtxReceiptsDone tail b) :
    TerminatingProgBoundedOn
      (fun s => (PtxReceiptsDone s ∧ LogsWorldOwned s (locN s "stable_logs") ∧
        locN s "stable_logs" ≠ 0 ∧
        ∃ w : BitVec 64, s.locals.lookup (ofString "stable_logs") = some (.val (.word w))) ∧
        TxBacking s)
      (spinePlug 2 (spineAt 137 ptxCode) tail) (K.lst_push + b + 1) := by
  have hs : TerminatingProgBoundedOn Phase4ReceiptSlotReady
      (.seq (.store (.var .local (ofString "rl")) (.var .local (ofString "stable_logs"))) tail) b := by
    intro F s hc hp
    have hb := seq_bound_trans (a := 0) (fun u _ _ _ => by
      have hu := clock_store u (.var .local (ofString "rl")) (.var .local (ofString "stable_logs"))
      exact ⟨by omega, by omega⟩) hoare_receiptSlot_store htail s hc hp
    simpa only [Nat.zero_add] using hb
  have he : spinePlug 2 (spineAt 137 ptxCode) tail =
      .decCall (ofString "rl") .one (ofString "lst_push")
        [.load .one (.op .add [.var .global (ofString "bo"), .const 72]), .const 8]
        (.seq (.store (.var .local (ofString "rl")) (.var .local (ofString "stable_logs"))) tail) := by
    unfold ptxCode
    rfl
  rw [he]
  intro F s hc hp
  exact TerminatingProgBoundedOn.decCall_on
    h.fb_lst_push _ _ _
    (fun t vs body callee ret hc hp ha hl => guestInv_callEntry t callee hp.1.1.1.1.1.1)
    (resume_lst_push_owned_receiptSlot_backing h) hs s hc hp

/-- The receipt prefix, log pushing, allocation, and stable copying compose. -/
theorem phase4ThroughStableCopy_typed_cut (h : PtxCallees)
    (hresume : DecCallResumeOn Phase4TypedLogPointers
      (fun s => Phase4LogSlotReady s ∧
        (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
        ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p)))
      (ofString "slot") (ofString "lst_push")
      [.load .one (.op .add [.var .global (ofString "bo"), .const 40]), .const 8])
    {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn PtxReceiptsDone tail b) :
    TerminatingProgBoundedOn TxAfterCallStrong
      (spinePlug 38 (spineAt 99 ptxCode) tail)
      (phase4CreditCost + (K.max + 1) + ((K.lst_new + 1) +
        (K.encode_receipt + ((2 ^ 64 + 1) * ((K.lst_push + 1) + 1) +
          (K.lst_new + (2 ^ 28 + 1 + b) + 1)) + 1))) := by
  have hb := @phase4ThroughCapacity_typed_cut h hresume _ _
    (stable_allocation_decl_loop_cut h htail)
  have he : spinePlug 38 (spineAt 99 ptxCode) tail =
      spinePlug 33 (spineAt 99 ptxCode) (spinePlug 5 (spineAt 132 ptxCode) tail) := by
    unfold ptxCode
    rfl
  rw [he]
  intro F s hc hp
  exact hb s hc hp

/-- The complete prefix delivers stable receipts with their world ownership. -/
theorem phase4ThroughStableCopy_owned_cut (h : PtxCallees)
    (hresume : DecCallResumeOn Phase4TypedLogPointers
      (fun s => Phase4LogSlotReady s ∧
        (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
        ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p)))
      (ofString "slot") (ofString "lst_push")
      [.load .one (.op .add [.var .global (ofString "bo"), .const 40]), .const 8])
    {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn
      (fun s => PtxReceiptsDone s ∧ LogsWorldOwned s (locN s "stable_logs") ∧
        locN s "stable_logs" ≠ 0 ∧
        ∃ w : BitVec 64, s.locals.lookup (ofString "stable_logs") = some (.val (.word w))) tail b) :
    TerminatingProgBoundedOn TxAfterCallStrong
      (spinePlug 38 (spineAt 99 ptxCode) tail)
      (phase4CreditCost + (K.max + 1) + ((K.lst_new + 1) +
        (K.encode_receipt + ((2 ^ 64 + 1) * ((K.lst_push + 1) + 1) +
          (K.lst_new + (2 ^ 28 + 1 + b) + 1)) + 1))) := by
  have hb := @phase4ThroughCapacity_typed_cut h hresume _ _
    (stable_allocation_decl_loop_owned_cut h htail)
  have he : spinePlug 38 (spineAt 99 ptxCode) tail =
      spinePlug 33 (spineAt 99 ptxCode) (spinePlug 5 (spineAt 132 ptxCode) tail) := by
    unfold ptxCode
    rfl
  rw [he]
  intro F s hc hp
  exact hb s hc hp

/-- The existing slot-return proof also retains the typed source operands. -/
theorem resume_lst_push_typed_logSlot (h : PtxCallees)
    (hnonzero : LstPushBackingNonzero) :
    DecCallResumeOn Phase4TypedLogPointers
      (fun s => Phase4LogSlotReady s ∧
        (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
        ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p)))
      (ofString "slot") (ofString "lst_push")
      [.load .one (.op .add [.var .global (ofString "bo"), .const 40]), .const 8] := by
  intro F s vs body callee ret v post hc hp ha hl hr
  refine ⟨resume_lst_push_logSlot h hnonzero s vs body callee ret v post hc hp.1 ha hl hr,
    ?_, ?_⟩
  · obtain ⟨n, hn⟩ := hp.2.1
    exact ⟨n, by simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "slot" ≠ ofString "nl" by decide] using hn⟩
  · obtain ⟨p, hp⟩ := hp.2.2.2
    exact ⟨p, by simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "slot" ≠ ofString "lp" by decide] using hp⟩

/-- Strong push backing also retains the typed source operands. -/
theorem resume_lst_push_typed_logSlot_backing (h : PtxCallees) :
    DecCallResumeOn (fun s => Phase4TypedLogPointers s ∧ TxBacking s)
      (fun s => Phase4LogSlotReady s ∧
        (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
        ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p)))
      (ofString "slot") (ofString "lst_push")
      [.load .one (.op .add [.var .global (ofString "bo"), .const 40]), .const 8] := by
  intro F s vs body callee ret v post hc hp ha hl hr
  refine ⟨resume_lst_push_logSlot_backing h s vs body callee ret v post hc
    ⟨hp.1.1, hp.2⟩ ha hl hr, ?_, ?_⟩
  · obtain ⟨n, hn⟩ := hp.1.2.1
    exact ⟨n, by simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "slot" ≠ ofString "nl" by decide] using hn⟩
  · obtain ⟨p, hp⟩ := hp.1.2.2.2
    exact ⟨p, by simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "slot" ≠ ofString "lp" by decide] using hp⟩

/-- The owned copy prefix closes Phase 4 given nonzero push backing. -/
theorem ptxPhase4_cut_strong_of_backing_nonzero (h : PtxCallees)
    (hnonzero : LstPushBackingNonzero)
    {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn PtxReceiptsDone tail b) :
    TerminatingProgBoundedOn TxAfterCallStrong (ptxPhase4 tail) (ptxCost4 + b) := by
  have hb := @phase4ThroughStableCopy_owned_cut h
    (resume_lst_push_typed_logSlot h hnonzero) _ _
    (phase4ReceiptPush_owned_cut h hnonzero htail)
  have he : ptxPhase4 tail =
      spinePlug 38 (spineAt 99 ptxCode) (spinePlug 2 (spineAt 137 ptxCode) tail) := by
    unfold ptxPhase4 ptxCode
    rfl
  rw [he]
  intro F s hc hp
  apply (hb s hc hp).weaken
  unfold phase4CreditCost ptxCost4
  simp only [Nat.max_eq_left (Nat.zero_le _)]
  omega

/-- Full Phase-4 composition with the two push preservation obligations explicit. -/
theorem ptxPhase4_cut_strong_of_slots (h : PtxCallees)
    (hlogs : DecCallResumeOn Phase4TypedLogPointers
      (fun s => Phase4LogSlotReady s ∧
        (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
        ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p)))
      (ofString "slot") (ofString "lst_push")
      [.load .one (.op .add [.var .global (ofString "bo"), .const 40]), .const 8])
    (R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (hreceipt : DecCallResumeOn PtxReceiptsDone R (ofString "rl") (ofString "lst_push")
      [.load .one (.op .add [.var .global (ofString "bo"), .const 72]), .const 8])
    (hstore : Hoare R
      (.store (.var .local (ofString "rl")) (.var .local (ofString "stable_logs")))
      (fun r t => r = none → PtxReceiptsDone t))
    {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn PtxReceiptsDone tail b) :
    TerminatingProgBoundedOn TxAfterCallStrong (ptxPhase4 tail) (ptxCost4 + b) := by
  have hb := @phase4ThroughStableCopy_typed_cut h hlogs _ _
    (phase4ReceiptPush_cut h R hreceipt hstore htail)
  have he : ptxPhase4 tail =
      spinePlug 38 (spineAt 99 ptxCode) (spinePlug 2 (spineAt 137 ptxCode) tail) := by
    unfold ptxPhase4 ptxCode
    rfl
  rw [he]
  intro F s hc hp
  apply (hb s hc hp).weaken
  unfold phase4CreditCost ptxCost4
  simp only [Nat.max_eq_left (Nat.zero_le _)]
  omega

/-- Full Phase 4 with the concrete store proof and typed log return discharged. -/
theorem ptxPhase4_cut_strong_of_receipt_resume (h : PtxCallees)
    (hnonzero : LstPushBackingNonzero)
    (hreceipt : DecCallResumeOn PtxReceiptsDone Phase4ReceiptSlotReady
      (ofString "rl") (ofString "lst_push")
      [.load .one (.op .add [.var .global (ofString "bo"), .const 72]), .const 8])
    {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn PtxReceiptsDone tail b) :
    TerminatingProgBoundedOn TxAfterCallStrong (ptxPhase4 tail) (ptxCost4 + b) := by
  intro F s hc hp
  exact ptxPhase4_cut_strong_of_slots h (resume_lst_push_typed_logSlot h hnonzero)
    Phase4ReceiptSlotReady hreceipt hoare_receiptSlot_store htail s hc hp

/-- The concrete allocator call adds its callee budget before a copy-ready tail. -/
theorem stable_allocation_copy_cut (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn (fun t => StableLengthPre t ∧ StableCopySpatial t ∧
      locN t "logs" ≠ 0 ∧ WordsOK t (locN t "stable_logs", 24) ∧
      ∃ p : BitVec 64, t.locals.lookup (ofString "lp") = some (.val (.word p))) tail b) :
    TerminatingProgBoundedOn (fun s => Phase4StableCapReady s ∧
      (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
      locN s "logs" ≠ 0 ∧
      ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p)))
      (.seq (.call (some (some (.local, ofString "stable_logs"), none)) (ofString "lst_new")
        [.const 8, .var .local (ofString "stable_log_cap")]) tail)
      ((K.lst_new + 1) + b) := by
  refine seq_bound_trans (P := fun s => Phase4StableCapReady s ∧
    (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
    locN s "logs" ≠ 0 ∧
    ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p)))
    ?_ (hoare_lst_new_stable_copy h) htail
  intro F s hc hp
  exact TerminatingProgBoundedOn.call_on (P := fun t => Phase4StableCapReady t ∧
    (∃ n : BitVec 64, t.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
    locN t "logs" ≠ 0 ∧
    ∃ p : BitVec 64, t.locals.lookup (ofString "lp") = some (.val (.word p)))
    h.fb_lst_new _ _
    (fun t vs body callee ret hc hp ha hl => guestInv_callEntry t callee hp.1.1.1.1.1.1.1.1.1)
    s hc hp

/-- Allocation, length initialization, and the complete copy loop have one bound. -/
theorem stable_allocation_loop_cut (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn PtxReceiptsDone tail b) :
    TerminatingProgBoundedOn (fun s => Phase4StableCapReady s ∧
      (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
      locN s "logs" ≠ 0 ∧
      ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p)))
      (.seq (.call (some (some (.local, ofString "stable_logs"), none)) (ofString "lst_new")
        [.const 8, .var .local (ofString "stable_log_cap")])
        (.seq (.store (.op .add [.var .local (ofString "stable_logs"), .const 8])
          (.var .local (ofString "nl")))
          (.seq (.assign .local (ofString "stable_lp")
            (.load .one (.var .local (ofString "stable_logs"))))
            (.seq (.assign .local (ofString "i") (.const 0))
              (.seq (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl")))
                (.seq (.store (.op .add [.var .local (ofString "stable_lp"),
                  .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
                  (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))))
                tail))))) ((K.lst_new + 1) + (2 ^ 28 + 1 + b)) := by
  intro F s hc hp
  refine seq_bound_trans ?_ (hoare_lst_new_stable_joint h)
    (stable_length_setup_loop_cut htail) s hc hp
  intro G t hcode hpre
  exact TerminatingProgBoundedOn.call_on (P := fun u => Phase4StableCapReady u ∧
    (∃ n : BitVec 64, u.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
    locN u "logs" ≠ 0 ∧
    ∃ p : BitVec 64, u.locals.lookup (ofString "lp") = some (.val (.word p)))
    h.fb_lst_new _ _
    (fun u vs body callee ret hc hp ha hl => guestInv_callEntry u callee hp.1.1.1.1.1.1.1.1.1)
    t hcode hpre

/-- A nonempty copy obtains its typed length operand directly from positivity. -/
theorem lst_new_stable_length_pre_nonempty (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4StableCapReady s)
    (hn : 0 < locN s "nl")
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 8, .var .local (ofString "stable_log_cap")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    StableLengthPre (setVarHOLFinite (ofString "stable_logs") v {post with locals := s.locals}) := by
  exact lst_new_stable_length_pre h s vs body callee ret v post hc hp
    (stable_positive_local_word s "nl" hn) ha hl hr

theorem lookup_process_message_call :
    originalRuntimeCode.lookup (ofString "process_message_call") =
      some ((sourceFunctionEntry Guest.Software.guestFn_process_message_call).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 607 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_process_message_call) rfl

theorem msgReady_with_msg_local {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat)
    (hmsg : locals.lookup (ofString "msg") = s.locals.lookup (ofString "msg"))
    (h : MsgReady s) : MsgReady { s with locals := locals, clock := k } := by
  have hm := locN_congr s locals k "msg" hmsg
  obtain ⟨hA, S, hW, hm152, hm160, hin, hw, hd1, hd2, hav, hgas, hroles⟩ := h
  refine ⟨(arenaReady_with_locals s locals k).mpr hA, S,
    (worldTyped_with_locals s locals k S).mpr hW, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change memW s (locN { s with locals := locals, clock := k } "msg" + 152) ∈ S
    rw [hm]; exact hm152
  · change memW s (locN { s with locals := locals, clock := k } "msg" + 160) ∈ S
    rw [hm]; exact hm160
  · change Inside (locN { s with locals := locals, clock := k } "msg", 176) sourceBase (globN s "heap_ptr")
    rw [hm]; exact hin
  · change WordsOK s (locN { s with locals := locals, clock := k } "msg", 176)
    rw [hm]; exact hw
  · intro t ht i hi; rw [hm]; exact hd1 t ht i hi
  · intro j hj; rw [hm]; exact hd2 j hj
  · obtain ⟨Nd, hTr, hdTr⟩ := hav
    refine ⟨Nd, hTr, fun o ho j hj => ?_⟩
    change o ∈ [(locN { s with locals := locals, clock := k } "msg", 176)] at ho
    rw [hm] at ho; exact hdTr o ho j hj
  · change memW s (locN { s with locals := locals, clock := k } "msg" + 40) < 2 ^ 63
    rw [hm]; exact hgas
  · change RolesOK s S (worldRoleSlots s ++
      [(memW s (locN { s with locals := locals, clock := k } "msg" + 152), "frame.addr"),
       (memW s (locN { s with locals := locals, clock := k } "msg" + 160), "frame.key")])
      (journalRoleSlots s)
    rw [hm]; exact hroles

theorem msg_word_of_var_eval {F : Type} (s : PanSemStateFiniteExact 64 F) (mv : ValueHOL 64)
    (he : evalAt s (.var .local (ofString "m")) = some mv)
    (hsh : shapeEqHOL (shapeOfHOLExact mv) .one = true) :
    mv = .val (.word (BitVec.ofNat 64 (locN s "m"))) := by
  rw [shapeEqHOL_eq_true] at hsh
  obtain ⟨wm, rfl⟩ := shape_one_word hsh
  have hlu : s.locals.lookup (ofString "m") = some (.val (.word wm)) := by
    simpa [evalAt, evalHOLExact] using he
  have hloc : locN s "m" = wm.toNat := by simp [locN, hlu]
  rw [hloc, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem lookup_pmc_msg_value {F : Type} (s : PanSemStateFiniteExact 64 F)
    (vs : List (ValueHOL 64)) (body' : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL)
    (hc : s.code = originalRuntimeCode)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "m")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "process_message_call") vs =
      some (body', callee, ret')) :
    callee.lookup (ofString "msg") = some (.val (.word (BitVec.ofNat 64 (locN s "m")))) := by
  obtain ⟨mv, he, hm_lu⟩ := params_one_value s (ofString "process_message_call") (ofString "msg")
    .one _ .one (by rw [hc]; exact lookup_process_message_call)
    (.var .local (ofString "m")) vs body' callee ret' ha hl
  have ha' := ha
  rw [evalListHOLFinite_eq_toExact] at ha'
  simp only [evalListHOLExact, he, Option.some.injEq] at ha'
  subst ha'
  have hsh : shapeEqHOL (shapeOfHOLExact mv) .one = true := by
    unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hl
    split at hl
    · cases hl
    · rename_i exactBody exactLocals exactShape raw
      unfold lookupCodeHOLExact at raw
      have hlk : s.code.lookup (ofString "process_message_call") =
          some ([(ofString "msg", .one)], (sourceFunctionEntry Guest.Software.guestFn_process_message_call).2.2.1, .one) := by
        rw [hc]; exact lookup_process_message_call
      rw [hlk] at raw
      dsimp only at raw
      split at raw
      · rename_i hcond
        have hall := hcond.2.2
        simp [shapeEqHOL_eq_true] at hall ⊢
        exact hall.symm
      · cases raw
  rw [msg_word_of_var_eval s mv he hsh] at hm_lu
  exact hm_lu

theorem entry_pmc :
    CallEntryOn PtxMessageReady MsgReady (ofString "process_message_call")
      [.var .local (ofString "m")] := by
  intro F s vs body callee ret hc hP ha hl
  have hlu := lookup_pmc_msg_value s vs body callee ret hc ha hl
  let s_msg := setVarHOLFinite (ofString "msg") (.val (.word (BitVec.ofNat 64 (locN s "m")))) s
  have hs_lu : s_msg.locals.lookup (ofString "msg") =
      some (.val (.word (BitVec.ofNat 64 (locN s "m")))) := by
    simp [s_msg, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  exact msgReady_with_msg_local s_msg callee (s.clock - 1) (hlu.trans hs_lu.symm) hP.2

def pmcScratchSpec : List (String × Nat × Nat) :=
  [("b2_v", 128, 128), ("bn_expw", 352, 352), ("bn_gamma", 384, 384), ("evm_key_buf", 32, 32),
   ("keccak_pad", 136, 136), ("keccak_st", 200, 200), ("mpt_nib_scratch", 64, 64), ("pre_hdr_buf", 96, 96),
   ("rmd_h", 40, 40), ("rmd_pad", 128, 128), ("rmd_x", 128, 128), ("sha_pad", 128, 128),
   ("sha_st", 64, 64), ("sk_buf", 64, 52), ("u256_ws", 640, 640)]

theorem pmcScratchSpec_ok : ScratchSpec pmcScratchSpec := by
  unfold ScratchSpec pmcScratchSpec
  decide

/-- R11's conditional scratch footprint, with the strengthened return contract. -/
def PmcStrong : Prop :=
  WorldKeepsIn MsgReady
    (fun s => [memW s (locN s "msg" + 152), memW s (locN s "msg" + 160)])
    (fun s => (locN s "msg", 176) ::
      pmcScratchSpec.map (fun e => bufferRegion s (e.1, e.2.2)))
    ["bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr", "heap_ptr", "journal_n", "scratch_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]),
     ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    RetMessageOutputStrong (ofString "process_message_call")

theorem resume_pmc_strong (hwk_strong : PmcStrong) :
    DecCallResumeOn PtxMessageReady TxAfterCallStrong (ofString "out")
      (ofString "process_message_call") [.var .local (ofString "m")] := by
  intro F s vs body callee ret v post hc hP ha hl hb
  unfold PmcStrong at hwk_strong
  have hMR := entry_pmc s vs body callee ret hc hP ha hl
  have hwk := funSpec_at_lookup hwk_strong s hc vs body callee ret hl hMR (by rw [hb]; simp)
  rw [hb] at hwk; dsimp only at hwk
  have hwsi := hwk (Or.inl ⟨v, rfl⟩)
  obtain ⟨_, S, hWT_ce, hm152, hm160, _, _, hd_tab, hd_fix, hav_tr, _, _⟩ := hMR
  obtain ⟨Nd, hTr_ce, hd_tr⟩ := hav_tr
  have hWTW_ce : WorldTypedWith (callEntryStateHOLFinite s callee) S Nd :=
    ⟨hWT_ce.1, hWT_ce.2.1, hWT_ce.2.2.1, hTr_ce⟩
  have hmsg_disj_owned : ∀ j ∈ worldOwned (callEntryStateHOLFinite s callee) S Nd,
      Disj (locN (callEntryStateHOLFinite s callee) "msg", 176) j := by
    intro j hj
    unfold worldOwned at hj
    rcases List.mem_append.mp hj with h1 | hnd
    · rcases List.mem_append.mp h1 with htab | hfix
      · obtain ⟨t, ht, hi⟩ := List.mem_flatMap.mp htab
        exact hd_tab t ht j hi
      · exact hd_fix j hfix
    · exact hd_tr _ (by simp) j hnd
  let Rlist : List Ivl :=
    (locN (callEntryStateHOLFinite s callee) "msg", 176) ::
      pmcScratchSpec.map (fun e => bufferRegion (callEntryStateHOLFinite s callee) (e.1, e.2.2))
  have hR_disj : IvlsDisj Rlist (worldTypedIvls (callEntryStateHOLFinite s callee) S Nd) := by
    intro i hi j hj
    rcases List.mem_cons.mp hi with rfl | hi_gs
    · exact hmsg_disj_owned j (R13Shards.worldTypedIvls_sub_worldOwned hj)
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hi_gs
      obtain ⟨hgb, hnu, _, hle⟩ := pmcScratchSpec_ok e he
      exact bufferRegion_disj_le hWTW_ce (e.1, e.2.1) hgb hnu e.2.2 hle j hj
  have hT_in : ∀ t ∈ [memW (callEntryStateHOLFinite s callee) (locN (callEntryStateHOLFinite s callee) "msg" + 152),
      memW (callEntryStateHOLFinite s callee) (locN (callEntryStateHOLFinite s callee) "msg" + 160)], t ∈ S := by
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact hm152
    · exact hm160
  obtain ⟨hAp, _, hg_kept, hrec_kept, hwsi_step⟩ := hwsi
  obtain ⟨S', Nd', _, hWTW_post, _, _, hret_msg⟩ := hwsi_step S Nd hWTW_ce hT_in hR_disj
  obtain ⟨out, rfl, hw_out, hin_out, hdisj_out, hll_out⟩ := hret_msg.1 v rfl
  obtain ⟨out', heq, hlogs_disj⟩ := hret_msg.2 _ rfl
  have hout_eq : out = out' := by cases heq; rfl
  subst out'
  let resumed := setVarHOLFinite (ofString "out") (.val (.word out)) { post with locals := s.locals }
  have hW_resumed : WorldOK resumed :=
    worldOK_of_parts
      ((arenaReady_with_locals post resumed.locals post.clock).mpr hAp)
      ((R13Shards.worldTypedWith_with_locals post resumed.locals post.clock S' Nd').mpr hWTW_post)
  have hE := hP.1.2
  have hbo_eq : globN post "bo" = globN s "bo" :=
    R16Shards.globN_eq_of_lookup (hg_kept (ofString "bo") (by decide))
  have hjcap_eq : globN post "journal_cap" = globN s "journal_cap" :=
    R16Shards.globN_eq_of_lookup (hg_kept (ofString "journal_cap") (by decide))
  have hbo8 : globN s "bo" % 8 = 0 := (R13Shards.bo_words hWT_ce.2.2.1 hE.bo_nz).2.1
  have hR_bo : ∀ i ∈ Rlist, Disj i (globN s "bo", 88) :=
    fun i hi => hR_disj i hi _ (bo_mem_typed (s := callEntryStateHOLFinite s callee) hE.bo_nz)
  have hR_zero : ∀ i ∈ Rlist, i.2 = 0 → i.1 % 8 = 0 := by
    intro i hi hz
    rcases List.mem_cons.mp hi with rfl | hi_gs
    · simp at hz
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hi_gs
      exact bufferRegion_zero_aligned _ e.1 e.2.2 (by have := (pmcScratchSpec_ok e he).2.2.1; omega) hz
  have hkw : ∀ k ∈ ([24, 32, 40, 72, 80] : List Nat),
      memW post (globN s "bo" + k) = memW s (globN s "bo" + k) := by
    intro k hk
    have hoffs : k ∈ ([0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80] : List Nat) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk ⊢
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> simp
    have hrec_s : RecordsKept (fun _ => Rlist)
        [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]),
         ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
        s post := hrec_kept
    apply hrec_s ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (by simp) hE.bo_nz k hoffs
    intro i hi hch
    have hk_in : k + 8 ≤ 88 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> omega
    have hbase : (globN s "bo" + k) % 8 = 0 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> omega
    exact R13Shards.not_cellHits_of_disj hbase
      (fun hz => hR_zero i hi hz)
      ⟨by dsimp; omega, by dsimp; omega⟩
      (R13Shards.disj_symm (hR_bo i hi)) hch
  have hidx_lu : resumed.locals.lookup (ofString "index") = s.locals.lookup (ofString "index") := by
    simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "out" ≠ ofString "index" from by decide]
  have hi_eq : locN resumed "index" = locN s "index" :=
    locN_congr s resumed.locals post.clock "index" hidx_lu
  have hEnv_resumed : TxEnv resumed := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show globN post "bo" ≠ 0; rw [hbo_eq]; exact hE.bo_nz
    · show memW post (globN post "bo" + 24) ≠ 0; rw [hbo_eq, hkw 24 (by simp)]; exact hE.bo24
    · show memW post (globN post "bo" + 32) ≠ 0; rw [hbo_eq, hkw 32 (by simp)]; exact hE.bo32
    · show memW post (globN post "bo" + 40) ≠ 0; rw [hbo_eq, hkw 40 (by simp)]; exact hE.bo40
    · show memW post (globN post "bo" + 72) ≠ 0; rw [hbo_eq, hkw 72 (by simp)]; exact hE.bo72
    · show locN resumed "index" < memW post (globN post "bo" + 80)
      rw [hi_eq, hbo_eq, hkw 80 (by simp)]; exact hE.idx_lt
    · show globN post "journal_cap" ≠ 0; rw [hjcap_eq]; exact hE.jcap_nz
  have hout_loc : locN resumed "out" = out.toNat := by
    simp [resumed, locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  refine ⟨⟨hW_resumed, hEnv_resumed⟩, ?_, ?_, ?_, S', Nd',
    (R13Shards.worldTypedWith_with_locals post resumed.locals post.clock S' Nd').mpr hWTW_post, ?_, ?_⟩
  · change WordsOK post (locN resumed "out", 96)
    rw [hout_loc]; exact hw_out
  · change Inside (locN resumed "out", 96) sourceBase (globN post "heap_ptr")
    rw [hout_loc]; exact hin_out
  · change LogsListOK resumed (memW post (locN resumed "out" + 16))
    rw [hout_loc]
    exact (R13Shards.logsListOK_with_locals post resumed.locals post.clock _).mpr hll_out
  · change IvlsDisj [(locN resumed "out", 96)] (worldOwned post S' Nd')
    rw [hout_loc]; exact hdisj_out
  · change LogsLiveOwned post S' Nd' (memW post (locN resumed "out" + 16))
    rw [hout_loc]; exact hlogs_disj

end PtxP34

theorem ptxPhase3_cut_strong (h : PtxCallees) (hwk : PtxP34.PmcStrong)
    {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn TxAfterCallStrong tail b) :
    TerminatingProgBoundedOn PtxMessageReady (ptxPhase3 tail) (ptxCost3 + b) := by
  have hb : TerminatingProgBoundedOn PtxMessageReady (ptxPhase3 tail)
      (K.«process_message_call» + b + 1) := by
    unfold ptxPhase3 ptxCode
    exact TerminatingProgBoundedOn.decCall_on h.gb_process_message_call
      (ofString "out") .one [.var .local (ofString "m")]
      PtxP34.entry_pmc (PtxP34.resume_pmc_strong hwk) htail
  have he : K.«process_message_call» + b + 1 = ptxCost3 + b := by
    unfold ptxCost3; omega
  rw [he] at hb
  intro F s hc hp
  exact hb s hc hp

/-- The Phase-3 cut also transports the caller-local shapes required downstream. -/
theorem ptxPhase3_cut_strong_shapes (h : PtxCallees) (hwk : PtxP34.PmcStrong)
    {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn
      (fun s => TxAfterCallStrong s ∧ PtxPhase4LocalShapes s) tail b) :
    TerminatingProgBoundedOn (fun s => PtxMessageReady s ∧ PtxPhase4LocalShapes s)
      (ptxPhase3 tail) (ptxCost3 + b) := by
  have he : CallEntryOn (fun s => PtxMessageReady s ∧ PtxPhase4LocalShapes s)
      MsgReady (ofString "process_message_call") [.var .local (ofString "m")] := by
    intro F s vs body callee ret hc hp ha hl
    exact PtxP34.entry_pmc s vs body callee ret hc hp.1 ha hl
  have hr : DecCallResumeOn (fun s => PtxMessageReady s ∧ PtxPhase4LocalShapes s)
      (fun s => TxAfterCallStrong s ∧ PtxPhase4LocalShapes s) (ofString "out")
      (ofString "process_message_call") [.var .local (ofString "m")] := by
    intro F s vs body callee ret v post hc hp ha hl hb
    exact ⟨PtxP34.resume_pmc_strong hwk s vs body callee ret v post hc hp.1 ha hl hb,
      ptxPhase4LocalShapes_resume s post v hp.2⟩
  have hb : TerminatingProgBoundedOn
      (fun s => PtxMessageReady s ∧ PtxPhase4LocalShapes s) (ptxPhase3 tail)
      (K.«process_message_call» + b + 1) := by
    unfold ptxPhase3 ptxCode
    exact TerminatingProgBoundedOn.decCall_on h.gb_process_message_call
      (ofString "out") .one [.var .local (ofString "m")] he hr htail
  have heq : K.«process_message_call» + b + 1 = ptxCost3 + b := by
    unfold ptxCost3; omega
  rw [heq] at hb
  intro F s hc hp
  exact hb s hc hp

/-- Composition interface for the remaining Phase-4 proof and the shape-aware
Phase-1/2 prefix. Both missing cuts are explicit hypotheses here. -/
theorem gbody_process_transaction_strong_of_cuts
    (h : PtxCallees) (hwk : PtxP34.PmcStrong)
    (h12 : ∀ (tail : ProgHOL 64) (b : Nat),
      TerminatingProgBoundedOn (fun s => PtxMessageReady s ∧ PtxPhase4LocalShapes s) tail b →
      TerminatingProgBoundedOn TxReadyStrong (ptxPhase1 (ptxPhase2 tail))
        (ptxCost1 + (ptxCost2 + b)))
    (h4 : ∀ (tail : ProgHOL 64) (b : Nat),
      TerminatingProgBoundedOn PtxReceiptsDone tail b →
      TerminatingProgBoundedOn (fun s => TxAfterCallStrong s ∧ PtxPhase4LocalShapes s)
        (ptxPhase4 tail) (ptxCost4 + b)) :
    TerminatingFunBoundedOn TxReadyStrong (ofString "process_transaction")
      K.«process_transaction» := by
  refine ⟨_, _, _, ptx_lookup, ?_⟩
  have hb : TerminatingProgBoundedOn TxReadyStrong
      (ptxPhase1 (ptxPhase2 (ptxPhase3 (ptxPhase4 ptxPhase5))))
      (ptxCost1 + (ptxCost2 + (ptxCost3 + (ptxCost4 + ptxCost5)))) :=
    h12 _ _ (ptxPhase3_cut_strong_shapes h hwk
      (h4 _ _ (R13Shards.ptxPhase5_cut h)))
  rw [← ptx_phases_eq, ptx_cost_eq] at hb
  intro F s hc hp
  simpa only [ptxCode, sourceFunctionEntry, Guest.Software.guestFn_process_transaction,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural] using
    (hb (F := F) s hc hp)

open PtxP34 in
/-- Transaction composition now needs only the prefix and local push contracts. -/
theorem gbody_process_transaction_strong_of_h12_slots
    (h : PtxCallees) (hwk : PtxP34.PmcStrong)
    (h12 : ∀ (tail : ProgHOL 64) (b : Nat),
      TerminatingProgBoundedOn (fun s => PtxMessageReady s ∧ PtxPhase4LocalShapes s) tail b →
      TerminatingProgBoundedOn TxReadyStrong (ptxPhase1 (ptxPhase2 tail))
        (ptxCost1 + (ptxCost2 + b)))
    (hlogs : DecCallResumeOn Phase4TypedLogPointers
      (fun s => Phase4LogSlotReady s ∧
        (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
        ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p)))
      (ofString "slot") (ofString "lst_push")
      [.load .one (.op .add [.var .global (ofString "bo"), .const 40]), .const 8])
    (R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (hreceipt : DecCallResumeOn PtxReceiptsDone R (ofString "rl") (ofString "lst_push")
      [.load .one (.op .add [.var .global (ofString "bo"), .const 72]), .const 8])
    (hstore : Hoare R
      (.store (.var .local (ofString "rl")) (.var .local (ofString "stable_logs")))
      (fun r t => r = none → PtxReceiptsDone t)) :
    TerminatingFunBoundedOn TxReadyStrong (ofString "process_transaction")
      K.«process_transaction» := by
  apply gbody_process_transaction_strong_of_cuts h hwk h12
  intro tail b ht F s hc hp
  exact ptxPhase4_cut_strong_of_slots h hlogs R hreceipt hstore ht s hc hp.1

/-- The complete transaction bound, with the remaining backing contract explicit.
`BoListArg` and `TxReadyStrong` constrain list headers but do not assert that
their backing pointers are nonzero; that obligation must not be hidden by the
composition theorem. -/
theorem gbody_process_transaction_strong_of_h12_backing_nonzero
    (h : PtxCallees) (hwk : PtxP34.PmcStrong)
    (hnonzero : PtxP34.LstPushBackingNonzero)
    (h12 : ∀ (tail : ProgHOL 64) (b : Nat),
      TerminatingProgBoundedOn (fun s => PtxMessageReady s ∧ PtxPhase4LocalShapes s) tail b →
      TerminatingProgBoundedOn TxReadyStrong (ptxPhase1 (ptxPhase2 tail))
        (ptxCost1 + (ptxCost2 + b))) :
    TerminatingFunBoundedOn TxReadyStrong (ofString "process_transaction")
      K.«process_transaction» := by
  apply gbody_process_transaction_strong_of_cuts h hwk h12
  intro tail b ht F s hc hp
  exact PtxP34.ptxPhase4_cut_strong_of_backing_nonzero h hnonzero ht s hc hp.1

/-- Phase 3 carries both backing facts under an explicit callee preservation
contract, together with the existing strong message result and local shapes. -/
theorem ptxPhase3_cut_backing_strong_shapes (h : PtxCallees) (hwk : PtxP34.PmcStrong)
    (hback : DecCallResumeOn (fun s => PtxMessageReady s ∧ TxBacking s)
      TxBacking (ofString "out") (ofString "process_message_call") [.var .local (ofString "m")])
    {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn
      (fun s => TxAfterCallBackingStrong s ∧ PtxPhase4LocalShapes s) tail b) :
    TerminatingProgBoundedOn
      (fun s => (PtxMessageReady s ∧ TxBacking s) ∧ PtxPhase4LocalShapes s)
      (ptxPhase3 tail) (ptxCost3 + b) := by
  have he : CallEntryOn
      (fun s => (PtxMessageReady s ∧ TxBacking s) ∧ PtxPhase4LocalShapes s)
      MsgReady (ofString "process_message_call") [.var .local (ofString "m")] := by
    intro F s vs body callee ret hc hp ha hl
    exact PtxP34.entry_pmc s vs body callee ret hc hp.1.1 ha hl
  have hr : DecCallResumeOn
      (fun s => (PtxMessageReady s ∧ TxBacking s) ∧ PtxPhase4LocalShapes s)
      (fun s => TxAfterCallBackingStrong s ∧ PtxPhase4LocalShapes s)
      (ofString "out") (ofString "process_message_call") [.var .local (ofString "m")] := by
    intro F s vs body callee ret v post hc hp ha hl hb
    exact ⟨⟨PtxP34.resume_pmc_strong hwk s vs body callee ret v post hc hp.1.1 ha hl hb,
      hback s vs body callee ret v post hc hp.1 ha hl hb⟩,
      ptxPhase4LocalShapes_resume s post v hp.2⟩
  have hb : TerminatingProgBoundedOn
      (fun s => (PtxMessageReady s ∧ TxBacking s) ∧ PtxPhase4LocalShapes s)
      (ptxPhase3 tail) (K.«process_message_call» + b + 1) := by
    unfold ptxPhase3 ptxCode
    exact TerminatingProgBoundedOn.decCall_on h.gb_process_message_call
      (ofString "out") .one [.var .local (ofString "m")] he hr htail
  have heq : K.«process_message_call» + b + 1 = ptxCost3 + b := by
    unfold ptxCost3; omega
  rw [heq] at hb
  intro F s hc hp
  exact hb s hc hp

/-- Parameterized backing-aware transaction export. The prefix, message-call
backing preservation, and Phase-4 cut remain explicit integration obligations;
the weaker world contracts alone do not imply them. -/
theorem gbody_process_transaction_backing_strong_of_h12
    (h : PtxCallees) (hwk : PtxP34.PmcStrong)
    (hback : DecCallResumeOn (fun s => PtxMessageReady s ∧ TxBacking s)
      TxBacking (ofString "out") (ofString "process_message_call") [.var .local (ofString "m")])
    (h12 : ∀ (tail : ProgHOL 64) (b : Nat),
      TerminatingProgBoundedOn
        (fun s => (PtxMessageReady s ∧ TxBacking s) ∧ PtxPhase4LocalShapes s) tail b →
      TerminatingProgBoundedOn TxReadyBackingStrong (ptxPhase1 (ptxPhase2 tail))
        (ptxCost1 + (ptxCost2 + b)))
    (h4 : ∀ (tail : ProgHOL 64) (b : Nat),
      TerminatingProgBoundedOn PtxReceiptsDone tail b →
      TerminatingProgBoundedOn (fun s => TxAfterCallBackingStrong s ∧ PtxPhase4LocalShapes s)
        (ptxPhase4 tail) (ptxCost4 + b)) :
    TerminatingFunBoundedOn TxReadyBackingStrong (ofString "process_transaction")
      K.«process_transaction» := by
  refine ⟨_, _, _, ptx_lookup, ?_⟩
  have hb : TerminatingProgBoundedOn TxReadyBackingStrong
      (ptxPhase1 (ptxPhase2 (ptxPhase3 (ptxPhase4 ptxPhase5))))
      (ptxCost1 + (ptxCost2 + (ptxCost3 + (ptxCost4 + ptxCost5)))) :=
    h12 _ _ (ptxPhase3_cut_backing_strong_shapes h hwk hback
      (h4 _ _ (R13Shards.ptxPhase5_cut h)))
  rw [← ptx_phases_eq, ptx_cost_eq] at hb
  intro F s hc hp
  simpa only [ptxCode, sourceFunctionEntry, Guest.Software.guestFn_process_transaction,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural] using
    (hb (F := F) s hc hp)

open PtxP34

/-- Stable-copy exit guard consumed by the proved receipt push/store suffix. -/
def Phase4StableBackingReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => (PtxReceiptsDone s ∧ LogsWorldOwned s (locN s "stable_logs") ∧
    locN s "stable_logs" ≠ 0 ∧
    ∃ w : BitVec 64, s.locals.lookup (ofString "stable_logs") = some (.val (.word w))) ∧
    TxBacking s

/-- Remaining Phase-4 integration obligation: retain backing through the
credit, log-push, allocation and stable-copy prefix. -/
def Phase4BackingPrefix : Prop :=
  ∀ (tail : ProgHOL 64) (b : Nat),
    TerminatingProgBoundedOn Phase4StableBackingReady tail b →
    TerminatingProgBoundedOn (fun s => TxAfterCallBackingStrong s ∧ PtxPhase4LocalShapes s)
      (spinePlug 38 (spineAt 99 ptxCode) tail)
      (phase4CreditCost + (K.max + 1) + ((K.lst_new + 1) +
        (K.encode_receipt + ((2 ^ 64 + 1) * ((K.lst_push + 1) + 1) +
          (K.lst_new + (2 ^ 28 + 1 + b) + 1)) + 1)))

/-- Close Phase 4 from its backing-aware prefix and the concrete receipt suffix. -/
theorem ptxPhase4_cut_backing_strong (h : PtxCallees)
    (hprefix : Phase4BackingPrefix)
    {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn PtxReceiptsDone tail b) :
    TerminatingProgBoundedOn (fun s => TxAfterCallBackingStrong s ∧ PtxPhase4LocalShapes s)
      (ptxPhase4 tail) (ptxCost4 + b) := by
  have he : ptxPhase4 tail =
      spinePlug 38 (spineAt 99 ptxCode) (spinePlug 2 (spineAt 137 ptxCode) tail) := by
    unfold ptxPhase4 ptxCode
    rfl
  rw [he]
  intro F s hc hp
  have hb := hprefix _ _ (phase4ReceiptPush_backing_cut h htail) (F := F)
  apply (hb s hc hp).weaken
  unfold phase4CreditCost ptxCost4
  simp only [Nat.max_eq_left (Nat.zero_le _)]
  omega

/-- The quantified Phase-4 interface expected by transaction composition. -/
theorem h4_backing_strong (h : PtxCallees) (hprefix : Phase4BackingPrefix) :
    ∀ (tail : ProgHOL 64) (b : Nat),
      TerminatingProgBoundedOn PtxReceiptsDone tail b →
      TerminatingProgBoundedOn (fun s => TxAfterCallBackingStrong s ∧ PtxPhase4LocalShapes s)
        (ptxPhase4 tail) (ptxCost4 + b) := by
  intro tail b ht F s hc hp
  exact ptxPhase4_cut_backing_strong h hprefix ht s hc hp

/-- Callee-level backing contract for the cross-shard message-call bridge. -/
def PmcBackingStrong : Prop :=
  FunSpec (fun s => MsgReady s ∧ TxBacking s)
    (fun _ r post => ∀ v, r = some (.returned v) → TxBacking post)
    (ofString "process_message_call")

/-- Convert callee backing preservation to the caller resume obligation. -/
theorem resume_pmc_backing (hkeep : PmcBackingStrong) :
    DecCallResumeOn (fun s => PtxMessageReady s ∧ TxBacking s)
      TxBacking (ofString "out") (ofString "process_message_call") [.var .local (ofString "m")] := by
  intro F s vs body callee ret v post hc hp ha hl hb
  have hm := entry_pmc s vs body callee ret hc hp.1 ha hl
  have hpre : MsgReady (callEntryStateHOLFinite s callee) ∧
      TxBacking (callEntryStateHOLFinite s callee) := ⟨hm, hp.2⟩
  have hk := PtxP1.funSpec_at_lookup hkeep s hc vs body callee ret hl hpre (by rw [hb]; simp)
  rw [hb] at hk
  exact hk v rfl

namespace PtxP34

/-- Block-total stores preserve both nested backing words: the list headers
are disjoint from the block-output record by fixed-object separation. -/
theorem txAfterCallBackingStrong_store_bo {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : TxAfterCallBackingStrong s) {off : Nat} (hoff : off ∈ ([0, 8, 16, 48] : List Nat))
    {x : BitVec 64} (hx : s.memaddrs x) (hxe : x.toNat = globN s "bo" + off)
    {mem' : BitVec 64 → HolWordLab 64} (hm : ∀ a, a ≠ x → mem' a = s.memory a) :
    TxAfterCallBackingStrong {s with memory := mem'} := by
  refine ⟨txAfterCallStrong_store_bo h.1 hoff hx hxe hm, ?_⟩
  obtain ⟨S, Nd, hW, _⟩ := h.1.2.2.2.2
  have hE := h.1.1.2
  have hA := h.1.1.1.1
  obtain ⟨_, _, hgb_rest, _, _⟩ := fixedObjects_disj_parts hW.2.2.1
  have hbo_hi := (ivl_allocated_bound hA.2 (bo_words hW.2.2.1 hE.bo_nz).1).2
  have hbo_gbs : (globN s "bo", 88) ∈
      (globalBuffers.map fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) :=
    List.mem_map.2 ⟨("bo", 88), by decide, by simp [hE.bo_nz]⟩
  apply txBacking_store h.2 hm
  · intro k hk heq
    have ht := congrArg BitVec.toNat heq
    have hb : globN s "bo" + k < 2 ^ 64 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      dsimp at hbo_hi
      rcases hk with rfl | rfl <;> omega
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb, hxe] at ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk hoff
    rcases hk with rfl | rfl <;> rcases hoff with rfl | rfl | rfl | rfl <;> omega
  · intro k hk heq
    have hd : Disj (globN s "bo", 88) (memW s (globN s "bo" + k), 24) := by
      apply hgb_rest _ hbo_gbs
      apply List.mem_append_left
      apply List.mem_append_right
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl
      · simp [blockOutObjects, hE.bo_nz, hE.bo40]
      · simp [blockOutObjects, hE.bo_nz, hE.bo72]
    have ht := congrArg BitVec.toNat heq
    have hb : memW s (globN s "bo" + k) < 2 ^ 64 := by
      unfold memW
      split
      rename_i w hw
      exact w.isLt
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb, hxe] at ht
    unfold Disj at hd
    dsimp at hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
    rcases hoff with rfl | rfl | rfl | rfl <;> omega

end PtxP34

namespace PtxP34

/-- Operational store rule retaining both block-output backing pointers. -/
theorem hoare_store_bo_total_backing (off : Nat) (hoff : off ∈ ([0, 8, 16, 48] : List Nat))
    (op : BinOp) (args : List (ExpHOL 64)) :
    Hoare TxAfterCallBackingStrong
      (.store (.op .add [.var .global (ofString "bo"), .const (BitVec.ofNat 64 off)])
        (.op op args)) (fun r t => r = none → TxAfterCallBackingStrong t) := by
  apply R13Shards.Hoare.store_fall
  intro F s x v mem' h hx hv hm
  obtain ⟨w, rfl⟩ := PtxP1.eval_is_word_op hv
  have hs := panMemStoresHOL_word_spec (s := s) (x := x) (w := .word w)
    (mem' := mem') (by simpa only [flattenHOL] using hm)
  apply txAfterCallBackingStrong_store_bo h hoff hs.1 _ hs.2.2
  have he := eval_add_global_const hx
  obtain ⟨S, Nd, hWT, _⟩ := h.1.2.2.2.2
  have hb := (ivl_allocated_bound h.1.1.1.1.2
    (bo_words hWT.2.2.1 h.1.1.2.bo_nz).1).2
  have hoff64 : off < 2 ^ 64 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
    rcases hoff with rfl | rfl | rfl | rfl <;> norm_num
  have hsum : globN s "bo" + off < 2 ^ 64 := by
    dsimp at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
    rcases hoff with rfl | rfl | rfl | rfl <;> omega
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff64, Nat.mod_eq_of_lt hsum] using he

/-- All four block-total writes carry backing into their continuation. -/
theorem phase4TotalStores_backing_cut {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn TxAfterCallBackingStrong tail b) :
    TerminatingProgBoundedOn TxAfterCallBackingStrong
      (spinePlug 5 (spineAt 114 ptxCode) tail) b := by
  have hb : TerminatingProgBoundedOn TxAfterCallBackingStrong
      (spinePlug 5 (spineAt 114 ptxCode) tail) (0 + (0 + (0 + (0 + b)))) := by
    unfold ptxCode
    refine seq_bound_trans (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
      (hoare_store_bo_total_backing 0 (by simp) _ _) ?_
    refine seq_bound_trans (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
      (hoare_store_bo_total_backing 8 (by simp) _ _) ?_
    refine seq_bound_trans (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
      (hoare_store_bo_total_backing 48 (by simp) _ _) ?_
    refine seq_bound_trans (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
      (hoare_store_bo_total_backing 16 (by simp) _ _) ?_
    change TerminatingProgBoundedOn TxAfterCallBackingStrong (.seq .skip tail) b
    intro F s hc hp hnt
    simpa only [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_skip] using
      htail s hc hp (by simpa only [evaluateHOLFiniteState_seq_line780,
        evaluateHOLFiniteState_skip] using hnt)
  intro F s hc hp
  simpa only [Nat.zero_add] using hb s hc hp

end PtxP34

namespace PtxP34
open PtxP1

theorem localsOnly_txAfterCallBackingStrong : LocalsOnly ["index", "out"] TxAfterCallBackingStrong := by
  intro F s locals k hl h
  exact ⟨txAfterCallStrong_with_locals s locals k
    (hl "index" (by simp)) (hl "out" (by simp)) h.1, h.2⟩

/-- Read-only calls retain backing as well as the strong output invariant. -/
theorem resume_ro_txAfterCallBackingStrong {fname name : MlS}
    (hro : ReadOnlyFn fname)
    (hne : ∀ k ∈ (["index", "out"] : List String), ofString k ≠ name)
    (args : List (ExpHOL 64)) :
    DecCallResumeOn TxAfterCallBackingStrong TxAfterCallBackingStrong name fname args := by
  intro F s vs body callee ret v post hc hp ha hl hb
  refine ⟨resume_ro_txAfterCallStrong hro hne args s vs body callee ret v post hc hp.1 ha hl hb, ?_⟩
  have hs := funSpec_at_lookup hro s hc vs body callee ret hl
    (guestInv_callEntry s callee hp.1.1.1.1.1) (by rw [hb]; simp)
  rw [hb] at hs
  have he := hs (Or.inl ⟨v, rfl⟩)
  dsimp only at he
  change TxBacking post
  rw [he]
  exact hp.2

/-- Gas normalization and block-total updates preserve both backing facts. -/
theorem phase4Totals_backing_cut (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn TxAfterCallBackingStrong tail b) :
    TerminatingProgBoundedOn TxAfterCallBackingStrong
      (spinePlug 9 (spineAt 110 ptxCode) tail) (K.max + b + 1) := by
  have hb : TerminatingProgBoundedOn TxAfterCallBackingStrong
      (spinePlug 9 (spineAt 110 ptxCode) tail) (0 + (K.max + b + 1)) := by
    unfold ptxCode
    refine TerminatingProgBoundedOn.dec_onLocals localsOnly_txAfterCallBackingStrong _ (by decide) _ _ ?_
    refine TerminatingProgBoundedOn.dec_onLocals localsOnly_txAfterCallBackingStrong _ (by decide) _ _ ?_
    refine seq_bound_trans (Q := TxAfterCallBackingStrong) ?_ ?_ ?_
    · exact TerminatingProgBoundedOn.ite_on
        (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s .local _ _))
        (TerminatingProgBoundedOn.of_clock clock_skip)
    · apply Hoare.ite
      · apply Hoare.mono (P' := TxAfterCallBackingStrong) _ (fun _ hp => hp.1)
        exact Hoare.assign
          (fun s v hp _ _ => LocalsOnly.setVar localsOnly_txAfterCallBackingStrong
            (name := ofString "tx_state_gas_nat") (by decide) v s hp)
          (fun _ _ hr => absurd hr (by simp))
      · exact Hoare.skip (fun _ hp _ => hp.1)
      · exact fun _ _ hr => absurd hr (by simp)
    · refine TerminatingProgBoundedOn.decCall_on h.fb_max _ _ _
        (fun t vs body callee ret hc hp ha hl => guestInv_callEntry t callee hp.1.1.1.1.1)
        (resume_ro_txAfterCallBackingStrong h.ro_max (by decide) _) ?_
      have hh := @phase4TotalStores_backing_cut tail b htail
      unfold ptxCode at hh
      intro F s hc hp
      exact hh s hc hp
  intro F s hc hp
  simpa only [Nat.zero_add] using hb s hc hp

end PtxP34

namespace PtxP34
open PtxP1

/-- Refund arithmetic transports backing; only the two mutating ether credits
require a strengthened preservation contract. -/
theorem phase4CreditPrefix_backing_cut (h : PtxCallees)
    (hcredit : ∀ args : List (ExpHOL 64), Hoare TxAfterCallBackingStrong
      (.call (some (none, none)) (ofString "create_ether") args)
      (fun r t => r = none → TxAfterCallBackingStrong t))
    {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn TxAfterCallBackingStrong tail b) :
    TerminatingProgBoundedOn TxAfterCallBackingStrong (phase4CreditPrefix tail)
      (phase4CreditCost + b) := by
  have he : ∀ fn args, CallEntryOn TxAfterCallBackingStrong GuestInv fn args := by
    intro fn args F s vs body callee ret hc hp ha hl
    exact guestInv_callEntry s callee hp.1.1.1.1.1
  have hb : TerminatingProgBoundedOn TxAfterCallBackingStrong (phase4CreditPrefix tail)
      (K.udiv_small5 + (K.min + (K.max + (K.fee_mul +
        (K.u256_sub + (K.fee_mul + ((K.create_ether + 1) +
          ((K.create_ether + 1) + b)) + 1) + 1) + 1) + 1) + 1) + 1) := by
    unfold phase4CreditPrefix ptxCode
    refine TerminatingProgBoundedOn.dec_onLocals localsOnly_txAfterCallBackingStrong _ (by decide) _ _ ?_
    refine TerminatingProgBoundedOn.decCall_on h.fb_udiv_small5 _ _ _ (he _ _)
      (resume_ro_txAfterCallBackingStrong h.ro_udiv_small5 (by decide) _) ?_
    refine TerminatingProgBoundedOn.decCall_on h.fb_min _ _ _ (he _ _)
      (resume_ro_txAfterCallBackingStrong h.ro_min (by decide) _) ?_
    refine TerminatingProgBoundedOn.dec_onLocals localsOnly_txAfterCallBackingStrong _ (by decide) _ _ ?_
    refine TerminatingProgBoundedOn.decCall_on h.fb_max _ _ _ (he _ _)
      (resume_ro_txAfterCallBackingStrong h.ro_max (by decide) _) ?_
    refine TerminatingProgBoundedOn.dec_onLocals localsOnly_txAfterCallBackingStrong _ (by decide) _ _ ?_
    refine TerminatingProgBoundedOn.decCall_on h.fb_fee_mul _ _ _ (he _ _)
      (resume_ro_txAfterCallBackingStrong h.ro_fee_mul (by decide) _) ?_
    refine TerminatingProgBoundedOn.decCall_on h.fb_u256_sub _ _ _ (he _ _)
      (resume_ro_txAfterCallBackingStrong h.ro_u256_sub (by decide) _) ?_
    refine TerminatingProgBoundedOn.decCall_on h.fb_fee_mul _ _ _ (he _ _)
      (resume_ro_txAfterCallBackingStrong h.ro_fee_mul (by decide) _) ?_
    refine seq_bound_trans ?_ (hcredit _) ?_
    · exact bound_mono (TerminatingProgBoundedOn.call_guestInv h.fb_create_ether none _)
        (fun s hp => hp.1.1.1.1.1)
    refine seq_bound_trans ?_ (hcredit _) htail
    exact bound_mono (TerminatingProgBoundedOn.call_guestInv h.fb_create_ether none _)
      (fun s hp => hp.1.1.1.1.1)
  have heq : K.udiv_small5 + (K.min + (K.max + (K.fee_mul +
        (K.u256_sub + (K.fee_mul + ((K.create_ether + 1) +
          ((K.create_ether + 1) + b)) + 1) + 1) + 1) + 1) + 1) + 1 =
      phase4CreditCost + b := by unfold phase4CreditCost; omega
  rw [heq] at hb
  intro F s hc hp
  exact hb s hc hp

end PtxP34

namespace PtxP34

/-- Compose the backing-aware refund prefix and the proved totals segment. -/
theorem phase4CreditTotals_backing_cut (h : PtxCallees)
    (hcredit : ∀ args : List (ExpHOL 64), Hoare TxAfterCallBackingStrong
      (.call (some (none, none)) (ofString "create_ether") args)
      (fun r t => r = none → TxAfterCallBackingStrong t))
    {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn TxAfterCallBackingStrong tail b) :
    TerminatingProgBoundedOn TxAfterCallBackingStrong
      (spinePlug 20 (spineAt 99 ptxCode) tail)
      (phase4CreditCost + (K.max + 1) + b) := by
  have hb := @phase4CreditPrefix_backing_cut h hcredit _ _ (phase4Totals_backing_cut h htail)
  have he : spinePlug 20 (spineAt 99 ptxCode) tail =
      phase4CreditPrefix (spinePlug 9 (spineAt 110 ptxCode) tail) := by
    unfold phase4CreditPrefix ptxCode
    rfl
  rw [he]
  intro F s hc hp
  have hr := hb s hc hp
  convert hr using 1 <;> omega

end PtxP34

namespace PtxP34

/-- Loading the live-log pointer retains both block-output backing facts. -/
theorem phase4ThroughLogs_backing_cut (h : PtxCallees)
    (hcredit : ∀ args : List (ExpHOL 64), Hoare TxAfterCallBackingStrong
      (.call (some (none, none)) (ofString "create_ether") args)
      (fun r t => r = none → TxAfterCallBackingStrong t))
    {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn (fun s => Phase4LogsReady s ∧ TxBacking s) tail b) :
    TerminatingProgBoundedOn TxAfterCallBackingStrong
      (spinePlug 21 (spineAt 99 ptxCode) tail)
      (phase4CreditCost + (K.max + 1) + b) := by
  have hl : TerminatingProgBoundedOn TxAfterCallBackingStrong
      (.dec (ofString "logs") .one
        (.load .one (.op .add [.var .local (ofString "out"), .const 16])) tail) b :=
    dec_bound_trans (fun s v hp he => ⟨phase4LogsReady_load s v hp.1 he, hp.2⟩) htail
  have hb := @phase4CreditTotals_backing_cut h hcredit _ _ hl
  have he : spinePlug 21 (spineAt 99 ptxCode) tail =
      spinePlug 20 (spineAt 99 ptxCode)
        (.dec (ofString "logs") .one
          (.load .one (.op .add [.var .local (ofString "out"), .const 16])) tail) := by
    unfold ptxCode
    rfl
  rw [he]
  intro F s hc hp
  exact hb s hc hp

end PtxP34

namespace PtxP34

/-- A concrete write footprint disjoint from the outer record and both nested
headers preserves backing. This applies to fresh-allocation frame contracts. -/
theorem txBacking_of_framed_headers {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {keep : List Ivl} {fresh : Ivl}
    (h : TxBacking s) (hbo : globN post "bo" = globN s "bo")
    (hbo8 : globN s "bo" % 8 = 0) (hbob : globN s "bo" + 88 ≤ 2 ^ 64)
    (hl8 : ∀ k ∈ ([40, 72] : List Nat), memW s (globN s "bo" + k) % 8 = 0)
    (hlb : ∀ k ∈ ([40, 72] : List Nat), memW s (globN s "bo" + k) + 24 ≤ 2 ^ 64)
    (hfr : FrameOutside s post keep fresh)
    (hk_al : ∀ j ∈ keep, j.1 % 8 = 0 ∧ j.2 % 8 = 0)
    (hf_al : fresh.1 % 8 = 0 ∧ fresh.2 % 8 = 0)
    (hbk : ∀ j ∈ keep, Disj (globN s "bo", 88) j)
    (hbf : Disj (globN s "bo", 88) fresh)
    (hlk : ∀ k ∈ ([40, 72] : List Nat), ∀ j ∈ keep,
      Disj (memW s (globN s "bo" + k), 24) j)
    (hlf : ∀ k ∈ ([40, 72] : List Nat),
      Disj (memW s (globN s "bo" + k), 24) fresh) : TxBacking post := by
  apply txBacking_of_unhit_headers h hbo hbo8 hbob
    (R16Shards.ivlUnhit_of_frameOutside_aligned hfr (by simp) hk_al hf_al hbk hbf) hl8 hlb
  intro k hk
  exact R16Shards.ivlUnhit_of_frameOutside_aligned hfr (by simp) hk_al hf_al (hlk k hk) (hlf k hk)

end PtxP34

namespace PtxP34

/-- Fresh heap writes cannot touch an already allocated heap or scratch region. -/
theorem allocated_unhit_fresh_heap {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {i : Ivl}
    (hA : ArenaOK s) (hAp : ArenaOK post)
    (hgrow : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hi : Allocated s i) (hinz : i.2 ≠ 0)
    (hfr : FrameOutside s post [(globN s "scratch_ptr", 0)]
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr")) :
    IvlUnhit s post i := by
  apply R16Shards.ivlUnhit_of_frameOutside_aligned hfr
  · exact fun hz => False.elim (hinz hz)
  · intro j hj
    simp only [List.mem_singleton] at hj
    subst j
    exact ⟨hA.2.2.2.2.2.2.2.1, by simp⟩
  · have hs := hA.2.2.2.2.2.1
    have hp := hAp.2.2.2.2.2.1
    exact ⟨hs, by dsimp; omega⟩
  · intro j hj
    simp only [List.mem_singleton] at hj
    subst j
    exact Or.inr (Or.inl rfl)
  · have hbound : globN post "heap_ptr" ≤ globN s "scratch_ptr" := by
      have hlim := hAp.2.1
      have hs := hA.2.2.1
      have hs' := hA.2.2.2.1
      have hsep : heapLimit ≤ scratchStart := by decide
      omega
    rcases hi with hi | hi
    · exact Or.inr (Or.inr (Or.inl hi.2))
    · apply Or.inr ∘ Or.inr ∘ Or.inr
      have := hi.1
      dsimp
      omega

end PtxP34

namespace PtxP34

/-- Fresh heap allocation preserves backing when the old record and headers
are allocated and aligned. -/
theorem txBacking_fresh_heap {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) (hAp : ArenaOK post) (h : TxBacking s)
    (hbo : globN post "bo" = globN s "bo")
    (hgrow : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hb : Allocated s (globN s "bo", 88)) (hb8 : globN s "bo" % 8 = 0)
    (hl : ∀ k ∈ ([40, 72] : List Nat),
      Allocated s (memW s (globN s "bo" + k), 24) ∧
      memW s (globN s "bo" + k) % 8 = 0)
    (hfr : FrameOutside s post [(globN s "scratch_ptr", 0)]
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr")) :
    TxBacking post := by
  apply txBacking_of_unhit_headers h hbo hb8 (ivl_allocated_bound hA hb).2
    (allocated_unhit_fresh_heap hA hAp hgrow hb (by simp) hfr)
    (fun k hk => (hl k hk).2)
    (fun k hk => (ivl_allocated_bound hA (hl k hk).1).2)
  intro k hk
  exact allocated_unhit_fresh_heap hA hAp hgrow (hl k hk).1 (by simp) hfr

end PtxP34

namespace PtxP34
open PtxP1

/-- World typing supplies all protected allocation and alignment premises. -/
theorem txBacking_fresh_heap_world {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hp : TxAfterCallBackingStrong s) (hAp : ArenaOK post)
    (hbo : globN post "bo" = globN s "bo")
    (hgrow : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hfr : FrameOutside s post [(globN s "scratch_ptr", 0)]
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr")) :
    TxBacking post := by
  obtain ⟨S, Nd, hW, _⟩ := hp.1.2.2.2.2
  have hE := hp.1.1.2
  have hb := bo_words hW.2.2.1 hE.bo_nz
  apply txBacking_fresh_heap hp.1.1.1.1.2 hAp hp.2 hbo hgrow hb.1 hb.2.1 _ hfr
  intro k hk
  have hm : (memW s (globN s "bo" + k), 24) ∈ fixedObjects s := by
    unfold fixedObjects
    apply List.mem_append_left
    apply List.mem_append_right
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · simp [blockOutObjects, hE.bo_nz, hE.bo40]
    · simp [blockOutObjects, hE.bo_nz, hE.bo72]
  have ht := (hW.2.2.1.1 _ hm).resolve_left (by simp)
  exact ⟨ht.1, ht.2.1⟩

/-- The concrete null-log allocation preserves both block-output backing words. -/
theorem lst_new_receiptReady_backing_resume (h : PtxCallees) :
    DecCallResumeOn TxAfterCallBackingStrong (fun s => Phase4ReceiptReady s ∧ TxBacking s)
      (ofString "logs") (ofString "lst_new") [.const 8, .const 1] := by
  intro F s vs body callee ret v post hc hp ha hl hr
  refine ⟨lst_new_receiptReady_resume h s vs body callee ret v post hc hp.1 ha hl hr, ?_⟩
  have hlc := R13Shards.lookup_lst_new
  rw [← hc] at hlc
  obtain ⟨_, he, hcap⟩ := callee_param_two_exp s (ofString "lst_new")
    (ofString "esz") (ofString "cap") .one .one _ _ hlc
    (.const 8) (.const 1) (.val (.word 8)) (.val (.word 1))
    vs body callee ret rfl rfl ha hl
  have hbody := lookupCodeHOLFinite_installed_body _ _ _ _ _ _ _ _ _ hlc hl
  have hbody' : body = InitECandidate.Solver.GuestTrapAndLookup.sourceFnBody
      Guest.Software.guestFn_lst_new := hbody
  let ent := callEntryStateHOLFinite s callee
  have hrun : evaluateHOLFiniteState ent
      (InitECandidate.Solver.GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_lst_new) =
      (some (.returned v), post) := by rw [← hbody']; exact hr
  have hprops := WkBal.lst_new_heap_props ent 8 1
    ⟨guestInv_callEntry s callee hp.1.1.1.1.1, hp.1.1.1.1.2⟩
    (by decide) (by decide) (by decide) (by decide) he hcap v
    (congrArg Prod.fst hrun)
  rw [hrun] at hprops
  obtain ⟨w, hv, hw, hw8, hwn, hmem, hlen, hcap', hheap, hgrow, hAR,
    hbe, hsp, hfp, hL, hobjs, hd, ha', hfr, hglob⟩ := hprops
  have hbo : globN post "bo" = globN s "bo" := by
    unfold globN
    rw [← hglob (ofString "bo") (by decide)]
    rfl
  exact txBacking_fresh_heap_world hp hAR.2 hbo (Nat.le_of_lt hgrow) hfr

/-- Both branches of null-log initialization retain backing. -/
theorem phase4NullLogs_backing_cut (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn (fun s => Phase4ReceiptReady s ∧ TxBacking s) tail b) :
    TerminatingProgBoundedOn (fun s => Phase4LogsReady s ∧ TxBacking s)
      (spinePlug 1 (spineAt 120 ptxCode) tail) ((K.lst_new + 1) + b) := by
  have hb : TerminatingProgBoundedOn (fun s => Phase4LogsReady s ∧ TxBacking s)
      (spinePlug 1 (spineAt 120 ptxCode) tail) (max (K.lst_new + 1) 0 + b) := by
    unfold ptxCode
    refine seq_bound_trans (P := fun s => Phase4LogsReady s ∧ TxBacking s)
      (Q := fun s => Phase4ReceiptReady s ∧ TxBacking s) ?_ ?_ htail
    · apply TerminatingProgBoundedOn.ite_on
      · exact TerminatingProgBoundedOn.call_on (P := fun s => Phase4LogsReady s ∧ TxBacking s)
          h.fb_lst_new _ _
          (fun s vs body callee ret hc hp ha hl => guestInv_callEntry s callee hp.1.1.1.1.1.1)
      · exact TerminatingProgBoundedOn.of_clock
          (P := fun s => Phase4LogsReady s ∧ TxBacking s) clock_skip
    · apply Hoare.ite
      · apply Hoare.mono (P' := TxAfterCallBackingStrong) _ (fun _ hp => ⟨hp.1.1.1, hp.1.2⟩)
        exact Hoare.callLocal_resume (lst_new_receiptReady_backing_resume h)
      · apply Hoare.skip
        intro F s hp _
        refine ⟨⟨hp.1.1.1, hp.1.1.2.2.1, hp.1.1.2.2.2, ?_⟩, hp.1.2⟩
        rw [hp.1.1.2.1]
        obtain ⟨S, Nd, hw, _, ho⟩ := hp.1.1.1.2.2.2.2
        exact ⟨S, Nd, hw, ho⟩
      · exact fun _ _ hr => absurd hr (by simp)
  intro F s hc hp
  simpa only [Nat.max_zero] using hb s hc hp

end PtxP34

namespace PtxP34
open PtxP1

theorem localsOnly_phase4ReceiptBackingReady :
    LocalsOnly ["index", "out", "logs"] (fun s => Phase4ReceiptReady s ∧ TxBacking s) := by
  intro F s locals k hl hp
  exact ⟨localsOnly_phase4ReceiptReady s locals k hl hp.1, hp.2⟩

/-- The success flag uses only locals and therefore retains backing. -/
theorem phase4Succeeded_backing_cut {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn (fun s => Phase4ReceiptReady s ∧ TxBacking s) tail b) :
    TerminatingProgBoundedOn (fun s => Phase4ReceiptReady s ∧ TxBacking s)
      (spinePlug 2 (spineAt 121 ptxCode) tail) b := by
  have hb : TerminatingProgBoundedOn (fun s => Phase4ReceiptReady s ∧ TxBacking s)
      (spinePlug 2 (spineAt 121 ptxCode) tail) (0 + b) := by
    unfold ptxCode
    refine TerminatingProgBoundedOn.dec_onLocals localsOnly_phase4ReceiptBackingReady _ (by decide) _ _ ?_
    refine seq_bound_trans (P := fun s => Phase4ReceiptReady s ∧ TxBacking s)
      (Q := fun s => Phase4ReceiptReady s ∧ TxBacking s) ?_ ?_ htail
    · exact TerminatingProgBoundedOn.ite_on
        (TerminatingProgBoundedOn.of_clock (P := fun s => Phase4ReceiptReady s ∧ TxBacking s)
          (fun s => clock_assign s .local _ _))
        (TerminatingProgBoundedOn.of_clock (P := fun s => Phase4ReceiptReady s ∧ TxBacking s) clock_skip)
    · apply Hoare.ite
      · apply Hoare.mono (P' := fun s => Phase4ReceiptReady s ∧ TxBacking s) _ (fun _ hp => hp.1)
        exact Hoare.assign
          (fun s v hp _ _ => LocalsOnly.setVar localsOnly_phase4ReceiptBackingReady
            (name := ofString "succeeded") (by decide) v s hp)
          (fun _ _ hr => absurd hr (by simp))
      · exact Hoare.skip (fun _ hp _ => hp.1)
      · exact fun _ _ hr => absurd hr (by simp)
  intro F s hc hp
  simpa only [Nat.zero_add] using hb s hc hp

/-- Compose the backing-aware prefix through the receipt-encoding entry. -/
theorem phase4BeforeReceipt_backing_cut (h : PtxCallees)
    (hcredit : ∀ args : List (ExpHOL 64), Hoare TxAfterCallBackingStrong
      (.call (some (none, none)) (ofString "create_ether") args)
      (fun r t => r = none → TxAfterCallBackingStrong t))
    {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn (fun s => Phase4ReceiptReady s ∧ TxBacking s) tail b) :
    TerminatingProgBoundedOn TxAfterCallBackingStrong
      (spinePlug 24 (spineAt 99 ptxCode) tail)
      (phase4CreditCost + (K.max + 1) + ((K.lst_new + 1) + b)) := by
  have hb := @phase4ThroughLogs_backing_cut h hcredit _ _
    (phase4NullLogs_backing_cut h (phase4Succeeded_backing_cut htail))
  have he : spinePlug 24 (spineAt 99 ptxCode) tail =
      spinePlug 21 (spineAt 99 ptxCode)
        (spinePlug 1 (spineAt 120 ptxCode)
          (spinePlug 2 (spineAt 121 ptxCode) tail)) := by
    unfold ptxCode
    rfl
  rw [he]
  intro F s hc hp
  exact hb s hc hp

end PtxP34

namespace PtxP34
open PtxP1

/-- Fresh allocations preserve backing using only the transaction world guard. -/
theorem txBacking_fresh_heap_txWorld {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hW : TxWorld s) (hback : TxBacking s) (hAp : ArenaOK post)
    (hbo : globN post "bo" = globN s "bo")
    (hgrow : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hfr : FrameOutside s post [(globN s "scratch_ptr", 0)]
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr")) :
    TxBacking post := by
  obtain ⟨S, hWT⟩ := hW.1.2
  have hE := hW.2
  have hb := bo_words hWT.2.2.1 hE.bo_nz
  apply txBacking_fresh_heap hW.1.1.2 hAp hback hbo hgrow hb.1 hb.2.1 _ hfr
  intro k hk
  have hm : (memW s (globN s "bo" + k), 24) ∈ fixedObjects s := by
    unfold fixedObjects
    apply List.mem_append_left
    apply List.mem_append_right
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · simp [blockOutObjects, hE.bo_nz, hE.bo40]
    · simp [blockOutObjects, hE.bo_nz, hE.bo72]
  have ht := (hWT.2.2.1.1 _ hm).resolve_left (by simp)
  exact ⟨ht.1, ht.2.1⟩

/-- Concrete list allocation retains backing for any positive aligned size. -/
theorem lst_new_txBacking_resume {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hW : TxWorld s) (hback : TxBacking s)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post))
    (esz cap : BitVec 64)
    (he : callee.lookup (ofString "esz") = some (.val (.word esz)))
    (hcap : callee.lookup (ofString "cap") = some (.val (.word cap)))
    (hepos : 1 ≤ esz.toNat) (hmul : esz.toNat * cap.toNat < 2 ^ 64)
    (hal : (esz.toNat * cap.toNat) % 8 = 0) (hcpos : 1 ≤ cap.toNat) :
    TxBacking post := by
  have hlc := R13Shards.lookup_lst_new
  rw [← hc] at hlc
  have hbody := lookupCodeHOLFinite_installed_body _ _ _ _ _ _ _ _ _ hlc hl
  have hbody' : body = InitECandidate.Solver.GuestTrapAndLookup.sourceFnBody
      Guest.Software.guestFn_lst_new := hbody
  let ent := callEntryStateHOLFinite s callee
  have hrun : evaluateHOLFiniteState ent
      (InitECandidate.Solver.GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_lst_new) =
      (some (.returned v), post) := by rw [← hbody']; exact hr
  have hprops := WkBal.lst_new_heap_props ent esz cap
    ⟨guestInv_callEntry s callee hW.1.1.1, hW.1.1.2⟩
    hepos hmul hal hcpos he hcap v (congrArg Prod.fst hrun)
  rw [hrun] at hprops
  obtain ⟨w, hv, hw, hw8, hwn, hmem, hlen, hcap', hheap, hgrow, hAR,
    hbe, hsp, hfp, hL, hobjs, hd, ha', hfr, hglob⟩ := hprops
  have hbo : globN post "bo" = globN s "bo" := by
    unfold globN
    rw [← hglob (ofString "bo") (by decide)]
    rfl
  exact txBacking_fresh_heap_txWorld hW hback hAR.2 hbo (Nat.le_of_lt hgrow) hfr

/-- The stable-log capacity guard discharges the variable allocation premises. -/
theorem lst_new_stable_txBacking_resume :
    DecCallResumeOn (fun s => Phase4StableCapReady s ∧ TxBacking s) TxBacking
      (ofString "stable_logs") (ofString "lst_new")
      [.const 8, .var .local (ofString "stable_log_cap")] := by
  intro F s vs body callee ret v post hc hp ha hl hr
  have hargs := lst_new_stable_args s vs body callee ret hc hp.1 ha hl
  have hlc := R13Shards.lookup_lst_new
  rw [← hc] at hlc
  have hpos := (phase4StableCap_bounds s hp.1).1
  obtain ⟨cap, hcap⟩ : ∃ cap : BitVec 64,
      s.locals.lookup (ofString "stable_log_cap") = some (.val (.word cap)) := by
    unfold locN at hpos
    split at hpos
    · rename_i w hw
      exact ⟨w, hw⟩
    · omega
  obtain ⟨_, he, hcap'⟩ := callee_param_two_exp s (ofString "lst_new")
    (ofString "esz") (ofString "cap") .one .one _ _ hlc
    (.const 8) (.var .local (ofString "stable_log_cap")) (.val (.word 8)) (.val (.word cap))
    vs body callee ret rfl hcap ha hl
  have hcapN : locN (callEntryStateHOLFinite s callee) "cap" = cap.toNat := by
    simp [locN, callEntryStateHOLFinite, hcap']
  have hbound : (8 : BitVec 64).toNat * cap.toNat < 2 ^ 64 := by
    simpa only [hargs.1, hcapN, show (8 : BitVec 64).toNat = 8 from rfl] using hargs.2.2.2
  have hpositive : 1 ≤ cap.toNat := by simpa only [hcapN] using hargs.2.2.1
  exact lst_new_txBacking_resume s vs body callee ret v post hc hp.1.1.1.1.1.1 hp.2 hl hr
    8 cap he hcap' (by decide) hbound (by simp) hpositive

end PtxP34

namespace PtxP34
open PtxP1

/-- A word write in a region separated from the fixed objects retains backing.
This exposes the spatial premise used by the stable length and copy writes. -/
theorem txBacking_store_disjoint_fixed {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hW : TxWorld s) (hback : TxBacking s) {i : Ivl} {x : BitVec 64}
    (hx : i.1 ≤ x.toNat ∧ x.toNat + 8 ≤ i.1 + i.2)
    (hd : ∀ j ∈ fixedObjects s, Disj i j)
    {mem' : BitVec 64 → HolWordLab 64} (hm : ∀ a, a ≠ x → mem' a = s.memory a) :
    TxBacking {s with memory := mem'} := by
  obtain ⟨S, hWT⟩ := hW.1.2
  have hb := bo_words hWT.2.2.1 hW.2.bo_nz
  have hbnd := (ivl_allocated_bound hW.1.1.2 hb.1).2
  have hbo : (globN s "bo", 88) ∈ fixedObjects s := by
    have hh := typedRecord_mem_fixedObjects s (r := ("bo", 88)) (by decide)
    simpa only [hW.2.bo_nz, ↓reduceIte] using hh
  have hh : ∀ k ∈ ([40, 72] : List Nat),
      (memW s (globN s "bo" + k), 24) ∈ fixedObjects s := by
    intro k hk
    unfold fixedObjects
    apply List.mem_append_left
    apply List.mem_append_right
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · simp [blockOutObjects, hW.2.bo_nz, hW.2.bo40]
    · simp [blockOutObjects, hW.2.bo_nz, hW.2.bo72]
  apply txBacking_store hback hm
  · intro k hk heq
    have ht := congrArg BitVec.toNat heq
    have hk' : k = 40 ∨ k = 72 := by simpa using hk
    have hlt : globN s "bo" + k < 2 ^ 64 := by dsimp at hbnd; omega
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at ht
    have hdis := hd _ hbo
    unfold Disj at hdis
    dsimp at hdis
    omega
  · intro k hk heq
    have ht := congrArg BitVec.toNat heq
    have hal := (hWT.2.2.1.1 _ (hh k hk)).resolve_left (by simp)
    have hbound := (ivl_allocated_bound hW.1.1.2 hal.1).2
    have hlt : memW s (globN s "bo" + k) < 2 ^ 64 := by dsimp at hbound; omega
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at ht
    have hdis := hd _ (hh k hk)
    unfold Disj at hdis
    dsimp at hdis
    omega

end PtxP34

namespace PtxP34
open PtxP1

/-- The concrete stable-list length write preserves both block-output backings. -/
theorem hoare_stable_length_txBacking :
    Hoare (fun s => StableLengthPre s ∧ TxBacking s)
      (.store (.op .add [.var .local (ofString "stable_logs"), .const 8])
        (.var .local (ofString "nl")))
      (fun r t => r = none → TxBacking t) := by
  refine R13Shards.Hoare.store_fall fun s x v mem' hp hx hv hst => ?_
  obtain ⟨hp, hback⟩ := hp
  have hlocal := hp.2.2.1
  have hnl := hp.2.2.2.1
  have hv' : v = .val (.word (BitVec.ofNat 64 (locN s "nl"))) := by
    change s.locals.lookup (ofString "nl") = some v at hv
    rw [hnl] at hv
    exact (Option.some.inj hv).symm
  subst v
  have hx' : x = BitVec.ofNat 64 (locN s "stable_logs" + 8) := by
    simp [evalAt, evalHOLExact, evalListHOLExact, hlocal, valueIsWord,
      valueWord, wordOpHOL, wordOp] at hx
    subst x
    apply BitVec.eq_of_toNat_eq
    have hb := stable_length_address_bound s hp.1.1.1.1.1.1.1.1.1.1.2 hp.2.1
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb.1] using hb.2
  subst x
  obtain ⟨hdom, _, hm⟩ := R13Shards.panMemStoresHOL_word_spec
    (by simpa only [flattenHOL] using hst)
  have hW : TxWorld s := hp.1.1.1.1.1.1.1.1
  have hb := (ivl_allocated_bound hW.1.1.2 hp.2.1).2
  have hlt : locN s "stable_logs" + 8 < 2 ^ 64 := by dsimp at hb; omega
  apply txBacking_store_disjoint_fixed hW hback (i := (locN s "stable_logs", 24)) _ _ hm
  · simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    constructor <;> omega
  · obtain ⟨S, Nd, _, _, hd, _⟩ := hp.2.2.2.2
    intro j hj
    apply hd j
    unfold worldOwned
    exact List.mem_append_left _ (List.mem_append_right _ hj)

end PtxP34

namespace PtxP34
open PtxP1

/-- Every stable-copy pointer write is separated from the transaction backings. -/
theorem hoare_stableCopy_store_txBacking :
    Hoare (fun s => StableCopyStorePre s ∧ TxBacking s)
      (.store (.op .add [.var .local (ofString "stable_lp"),
        .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
      (fun r t => r = none → TxBacking t) := by
  refine R13Shards.Hoare.store_fall fun s x v mem' hp hx hv hst => ?_
  obtain ⟨⟨hinv, hi, ⟨w, p, q, hw, hl, hq, hptr⟩,
    S, Nd, hW, ho, hworld, hh, hd, ha, he⟩, hback⟩ := hp
  have hx' := stable_copy_destination_address_eval s w q hinv hw hq hptr hi
  rw [hx] at hx'
  have hxe : x = BitVec.ofNat 64
      (memW s (locN s "stable_logs") + 8 * locN s "i") := by
    simpa using Option.some.inj hx'
  subst x
  obtain ⟨_, _, hm⟩ := stable_copy_store_semantics s mem' w p hinv hw hl hi v hv hst
  apply txBacking_store_disjoint_fixed hinv.1.1 hback
    (i := (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap")) _ _ hm
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (stableCopyInv_destination_bound s hinv hi).2]
    have hc := hinv.2.2.2.2.1
    constructor <;> dsimp <;> omega
  · intro j hj
    exact hworld j (List.mem_append_left _ (List.mem_append_right _ hj))

/-- The copy store and counter increment retain transaction backing. -/
theorem hoare_stableCopy_body_txBacking :
    Hoare (fun s => StableCopyStorePre s ∧ TxBacking s)
      (.seq (.store (.op .add [.var .local (ofString "stable_lp"),
        .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))
      (fun r t => r = none → TxBacking t) := by
  apply Hoare.seq_fall hoare_stableCopy_store_txBacking
  exact Hoare.assign (fun _ _ hp _ _ => txBacking_set_local _ _ hp)
    (fun _ _ hr => absurd hr (by simp))

/-- The complete stable-copy loop retains both transaction backings. -/
theorem hoare_stableCopy_loop_txBacking :
    Hoare (fun s => StableCopyLoopInv s ∧ TxBacking s)
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl")))
        (.seq (.store (.op .add [.var .local (ofString "stable_lp"),
          .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))))
      (fun r t => r = none → PtxReceiptsDone t ∧ TxBacking t) := by
  have hf := hoare_stableCopy_loop_done_frame TxBacking
    (fun _ hp => hp) hoare_stableCopy_body_txBacking
  exact ⟨fun s hc hp hnt hr => let h := hf.run s hc hp hnt hr; ⟨h.1, h.2.1⟩⟩

end PtxP34

namespace PtxP34
open PtxP1

/-- Stable-copy exit supplies the full backing-aware receipt continuation guard. -/
theorem hoare_stableCopy_loop_owned_txBacking :
    Hoare (fun s => (StableCopyLoopInv s ∧ StableCopyOwnedFrame s) ∧ TxBacking s)
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl")))
        (.seq (.store (.op .add [.var .local (ofString "stable_lp"),
          .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))))
      (fun r t => r = none → Phase4StableBackingReady t) := by
  refine ⟨fun s hc hp hnt hr => ?_⟩
  exact ⟨hoare_stableCopy_loop_owned.run s hc hp.1 hnt hr,
    (hoare_stableCopy_loop_txBacking.run s hc ⟨hp.1.1, hp.2⟩ hnt hr).2⟩

/-- The backing-aware stable-copy loop uses the same concrete clock budget. -/
theorem stableCopy_loop_owned_backing_cut {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn Phase4StableBackingReady tail b) :
    TerminatingProgBoundedOn
      (fun s => (StableCopyLoopInv s ∧ StableCopyOwnedFrame s) ∧ TxBacking s)
      (.seq
        (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl")))
          (.seq (.store (.op .add [.var .local (ofString "stable_lp"),
            .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
            (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))))
        tail) (2 ^ 28 + 1 + b) := by
  intro F s hc hp
  exact seq_bound_trans (fun t ht h => stableCopy_loop_budget t ht h.1.1)
    hoare_stableCopy_loop_owned_txBacking htail s hc hp

end PtxP34

namespace PtxP34
open PtxP1

/-- Scoped backing-pointer loading and counter initialization retain transaction backing. -/
theorem stableCopy_backing_decl_owned_txBacking_cut {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn
      (fun s => (StableCopyLoopInv s ∧ StableCopyOwnedFrame s) ∧ TxBacking s) tail b) :
    TerminatingProgBoundedOn (fun s => ((StableLengthPost s ∧ locN s "logs" ≠ 0 ∧
      WordsOK s (locN s "stable_logs", 24) ∧ Allocated s (locN s "stable_logs", 24) ∧
      locN s "nl" ≤ locN s "stable_log_cap" ∧ StableCopySpatial s ∧
      WordAt s (locN s "stable_logs") ∧ ∃ n p w : BitVec 64,
        s.locals.lookup (ofString "nl") = some (.val (.word n)) ∧
        s.locals.lookup (ofString "lp") = some (.val (.word p)) ∧
        s.locals.lookup (ofString "stable_logs") = some (.val (.word w))) ∧
      StableCopyOwnedFrame s) ∧ TxBacking s)
      (.dec (ofString "stable_lp") .one
        (.load .one (.op .add [.var .local (ofString "stable_logs"), .const 0]))
        (.seq (.assign .local (ofString "i") (.const 0)) tail)) b := by
  have hf := hoare_stableCopyOwnedFrame_assign (ofString "i") (.const 0)
    (by decide) (by decide) (by decide)
  have hback : Hoare TxBacking (.assign .local (ofString "i") (.const 0))
      (fun r t => r = none → TxBacking t) :=
    Hoare.assign (fun _ _ hp _ _ => txBacking_set_local _ _ hp)
      (fun _ _ hr => absurd hr (by simp))
  have hi : TerminatingProgBoundedOn (fun s =>
      (StableCopyLoopInv (setVarHOLFinite (ofString "i") (.val (.word 0)) s) ∧
      StableCopyOwnedFrame s) ∧ TxBacking s)
      (.seq (.assign .local (ofString "i") (.const 0)) tail) b := by
    intro F s hc hp
    have hj : Hoare (fun s =>
        (StableCopyLoopInv (setVarHOLFinite (ofString "i") (.val (.word 0)) s) ∧
        StableCopyOwnedFrame s) ∧ TxBacking s) (.assign .local (ofString "i") (.const 0))
        (fun r t => r = none → (StableCopyLoopInv t ∧ StableCopyOwnedFrame t) ∧ TxBacking t) :=
      ⟨fun t ht h hnt hr => ⟨⟨hoare_stableCopy_zero_entry.run t ht h.1.1 hnt hr,
        hf.run t ht h.1.2 hnt hr⟩, hback.run t ht h.2 hnt hr⟩⟩
    simpa only [Nat.zero_add] using seq_bound_trans (a := 0) (fun u _ _ _ => by
      have hu := clock_assign u .local (ofString "i") (.const 0)
      exact ⟨by omega, by omega⟩) hj htail s hc hp
  intro G t ht hpre
  refine dec_bound_trans (P := fun s => ((StableLengthPost s ∧ locN s "logs" ≠ 0 ∧
      WordsOK s (locN s "stable_logs", 24) ∧ Allocated s (locN s "stable_logs", 24) ∧
      locN s "nl" ≤ locN s "stable_log_cap" ∧ StableCopySpatial s ∧
      WordAt s (locN s "stable_logs") ∧ ∃ n p w : BitVec 64,
        s.locals.lookup (ofString "nl") = some (.val (.word n)) ∧
        s.locals.lookup (ofString "lp") = some (.val (.word p)) ∧
        s.locals.lookup (ofString "stable_logs") = some (.val (.word w))) ∧
      StableCopyOwnedFrame s) ∧ TxBacking s) (Q := fun s =>
      (StableCopyLoopInv (setVarHOLFinite (ofString "i") (.val (.word 0)) s) ∧
      StableCopyOwnedFrame s) ∧ TxBacking s) ?_ hi t ht hpre
  intro F s v hp he
  obtain ⟨⟨⟨hp, hz, hh, ha, hc, hs, hword, n, p, w, hn, hl, hw⟩, hframe⟩, hb⟩ := hp
  refine ⟨⟨?_, ?_⟩, hb⟩
  · apply stableCopyLoopInv_backing_init s hp hz hh ha hc hs n p w v hn hl hw hword
    simpa [evalAt, evalHOLExact, hw, valueIsWord, valueWord, evalListHOLExact,
      wordOpHOL, wordOp] using he
  · apply stableCopyOwnedFrame_with_locals s _ s.clock _ _ _ hframe
    all_goals simp [HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "stable_lp" ≠ ofString "logs" by decide,
      show ofString "stable_lp" ≠ ofString "stable_logs" by decide,
      show ofString "stable_lp" ≠ ofString "stable_log_cap" by decide]

end PtxP34

namespace PtxP34
open PtxP1

/-- Length storage, scoped setup and the entire copy loop preserve backing. -/
theorem stable_length_decl_loop_backing_cut {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn Phase4StableBackingReady tail b) :
    TerminatingProgBoundedOn (fun s => ((StableLengthPre s ∧ StableCopyOwnedFrame s ∧
      Disj (locN s "logs", 24)
        (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
      Disj (locN s "stable_logs", 24)
        (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
      Disj (memW s (locN s "logs"), 8 * memW s (locN s "logs" + 8))
        (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
      ∀ j, j < memW s (locN s "logs" + 8) →
        Disj (memW s (memW s (locN s "logs") + 8 * j), 40)
          (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap")) ∧
      locN s "logs" ≠ 0 ∧ WordsOK s (locN s "stable_logs", 24) ∧
      ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p))) ∧ TxBacking s)
      (spinePlug 4 (spineAt 133 ptxCode) tail) (2 ^ 28 + 1 + b) := by
  have he : spinePlug 4 (spineAt 133 ptxCode) tail =
    (.seq (.store (.op .add [.var .local (ofString "stable_logs"), .const 8])
      (.var .local (ofString "nl")))
      (.dec (ofString "stable_lp") .one
        (.load .one (.op .add [.var .local (ofString "stable_logs"), .const 0]))
        (.seq (.assign .local (ofString "i") (.const 0))
          (.seq (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl")))
            (.seq (.store (.op .add [.var .local (ofString "stable_lp"),
              .panop .mul [.var .local (ofString "i"), .const 8]]) phase4LogCopySrc)
              (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))))
            tail)))) := by
    unfold ptxCode phase4LogCopySrc
    rfl
  rw [he]
  intro F s hc hp
  have hs := hoare_stable_length_owned_copy_ready
  have hb := hoare_stable_length_txBacking
  simpa only [Nat.zero_add] using seq_bound_trans (a := 0)
    (P := fun s => ((StableLengthPre s ∧ StableCopyOwnedFrame s ∧
      Disj (locN s "logs", 24)
        (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
      Disj (locN s "stable_logs", 24)
        (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
      Disj (memW s (locN s "logs"), 8 * memW s (locN s "logs" + 8))
        (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap") ∧
      ∀ j, j < memW s (locN s "logs" + 8) →
        Disj (memW s (memW s (locN s "logs") + 8 * j), 40)
          (memW s (locN s "stable_logs"), 8 * locN s "stable_log_cap")) ∧
      locN s "logs" ≠ 0 ∧ WordsOK s (locN s "stable_logs", 24) ∧
      ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p))) ∧ TxBacking s)
    (fun t _ _ _ => by
      have ht := clock_store t (.op .add [.var .local (ofString "stable_logs"), .const 8])
        (.var .local (ofString "nl"))
      exact ⟨by omega, by omega⟩)
    (⟨fun t ht h hnt hr => ⟨hs.run t ht h.1 hnt hr,
      hb.run t ht ⟨h.1.1.1, h.2⟩ hnt hr⟩⟩)
    (stableCopy_backing_decl_owned_txBacking_cut
      (stableCopy_loop_owned_backing_cut htail)) s hc hp

end PtxP34

namespace PtxP34
open PtxP1

/-- Stable allocation through copy exit retains the full backing-aware guard. -/
theorem stable_allocation_decl_loop_backing_cut (h : PtxCallees)
    {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn Phase4StableBackingReady tail b) :
    TerminatingProgBoundedOn (fun s => (Phase4StableCapReady s ∧
      (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
      locN s "logs" ≠ 0 ∧
      ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p))) ∧ TxBacking s)
      (spinePlug 5 (spineAt 132 ptxCode) tail)
      (K.lst_new + (2 ^ 28 + 1 + b) + 1) := by
  have he : spinePlug 5 (spineAt 132 ptxCode) tail =
      .decCall (ofString "stable_logs") .one (ofString "lst_new")
        [.const 8, .var .local (ofString "stable_log_cap")]
        (spinePlug 4 (spineAt 133 ptxCode) tail) := by
    unfold ptxCode
    rfl
  rw [he]
  intro F s hc hp
  refine TerminatingProgBoundedOn.decCall_on
    (P := fun s => (Phase4StableCapReady s ∧
      (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
      locN s "logs" ≠ 0 ∧
      ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p))) ∧ TxBacking s)
    h.fb_lst_new _ _ _ ?_ ?_ (stable_length_decl_loop_backing_cut htail) s hc hp
  · intro G t vs body callee ret hc hp ha hl
    exact guestInv_callEntry t callee hp.1.1.1.1.1.1.1.1.1.1
  · intro G t vs body callee ret v post hc hp ha hl hr
    refine ⟨⟨lst_new_stable_length_joint_pre h t vs body callee ret v post hc hp.1.1
        (stable_length_canonical_operand t hp.1.2.1) ha hl hr,
      lst_new_stable_copy_operands h t vs body callee ret v post hc hp.1.1 hp.1.2.2.1 hp.1.2.2.2 ha hl hr⟩, ?_⟩
    exact lst_new_stable_txBacking_resume t vs body callee ret v post hc ⟨hp.1.1, hp.2⟩ ha hl hr

end PtxP34

namespace PtxP34
open PtxP1

/-- Capacity normalization retains the transaction backing frame. -/
theorem stable_capacity_copy_backing_cut {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn (fun s => (Phase4StableCapReady s ∧
      (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
      locN s "logs" ≠ 0 ∧
      ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p))) ∧ TxBacking s) tail b) :
    TerminatingProgBoundedOn (fun s => (Phase4StableCapInit s ∧
      (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
      locN s "logs" ≠ 0 ∧
      ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p))) ∧ TxBacking s)
      (.seq (.ite (.cmp .equal (.var .local (ofString "stable_log_cap")) (.const 0))
        (.assign .local (ofString "stable_log_cap") (.const 1)) .skip) tail) b := by
  have hb : Hoare TxBacking
      (.ite (.cmp .equal (.var .local (ofString "stable_log_cap")) (.const 0))
        (.assign .local (ofString "stable_log_cap") (.const 1)) .skip)
      (fun r t => r = none → TxBacking t) := by
    apply Hoare.ite
    · exact Hoare.assign (fun _ _ hp _ _ => txBacking_set_local _ _ hp.1)
        (fun _ _ hr => absurd hr (by simp))
    · exact Hoare.skip (fun _ hp _ => hp.1)
    · exact fun _ _ hr => absurd hr (by simp)
  intro F s hc hp
  rw [← Nat.zero_add b]
  refine seq_bound_trans (P := fun s => (Phase4StableCapInit s ∧
      (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
      locN s "logs" ≠ 0 ∧
      ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p))) ∧ TxBacking s)
    ?_ ⟨fun t ht h hnt hr => ⟨hoare_phase4StableCap_copy_ready.run t ht h.1 hnt hr,
      hb.run t ht h.2 hnt hr⟩⟩ htail s hc hp
  intro G t ht hp
  exact TerminatingProgBoundedOn.ite_on (a := 0) (b := 0)
    (P := fun s => (Phase4StableCapInit s ∧
      (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
      locN s "logs" ≠ 0 ∧
      ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p))) ∧ TxBacking s)
    (fun u _ _ _ => by
      have hu := clock_assign u .local (ofString "stable_log_cap") (.const 1)
      exact ⟨by omega, by omega⟩)
    (fun u _ _ _ => by
      have hu := clock_skip u
      exact ⟨by omega, by omega⟩) t ht hp

/-- Capacity declaration and adjustment preserve backing and all copy operands. -/
theorem stable_capacity_setup_copy_backing_cut {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn (fun s => (Phase4StableCapReady s ∧
      (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
      locN s "logs" ≠ 0 ∧
      ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p))) ∧ TxBacking s) tail b) :
    TerminatingProgBoundedOn (fun s => (Phase4LogPointersReady s ∧
      (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
      locN s "logs" ≠ 0 ∧
      ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p))) ∧ TxBacking s)
      (spinePlug 2 (spineAt 130 ptxCode) tail) b := by
  unfold ptxCode
  intro F t hc ht
  refine dec_bound_trans (P := fun s => (Phase4LogPointersReady s ∧
    (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
    locN s "logs" ≠ 0 ∧
    ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p))) ∧ TxBacking s)
    ?_ (stable_capacity_copy_backing_cut htail) t hc ht
  intro F s v hp he
  obtain ⟨hn, hl⟩ := stable_capacity_copy_operands s v hp.1.2.1 hp.1.2.2.2
  refine ⟨⟨phase4StableCap_init s v hp.1.1 he, hn, ?_, hl⟩, hp.2⟩
  simpa [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
    show ofString "stable_log_cap" ≠ ofString "logs" by decide] using hp.1.2.2.1

end PtxP34

namespace PtxP34
open PtxP1

/-- Writes within the block-output log array cannot hit either backing header. -/
theorem txBacking_store_log_array {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hW : TxWorld s) (hback : TxBacking s) {x : BitVec 64}
    (hin : Inside (x.toNat, 8) (memW s (memW s (globN s "bo" + 40)))
      (memW s (memW s (globN s "bo" + 40)) +
        8 * memW s (memW s (globN s "bo" + 40) + 16)))
    {mem' : BitVec 64 → HolWordLab 64} (hm : ∀ a, a ≠ x → mem' a = s.memory a) :
    TxBacking {s with memory := mem'} := by
  obtain ⟨S, hWT⟩ := hW.1.2
  have hE := hW.2
  obtain ⟨_, hpw, hsep, _, _⟩ := fixedObjects_disj_parts hWT.2.2.1
  obtain ⟨_, _, hbo⟩ := blockOutObjects_eq_list hE hWT.1
  let arr := (memW s (memW s (globN s "bo" + 40)),
    8 * memW s (memW s (globN s "bo" + 40) + 16))
  have hpos : 8 * memW s (memW s (globN s "bo" + 40) + 16) ≠ 0 := by
    unfold Inside at hin
    dsimp at hin
    omega
  have hlen : (blockOutObjects s).length = 7 := by rw [hbo]; rfl
  have harr : (blockOutObjects s)[4]'(by omega) = arr := by
    simp [hbo, arr, hE.bo_nz, hback.1, hpos]
  have hmem : arr ∈ blockOutObjects s := harr ▸ List.getElem_mem (by omega : 4 < (blockOutObjects s).length)
  have hdbo : Disj (globN s "bo", 88) arr := by
    apply hsep _ (List.mem_map.2 ⟨("bo", 88), by decide, by simp [hE.bo_nz]⟩)
    exact List.mem_append_left _ (List.mem_append_right _ hmem)
  have hdhead : ∀ k ∈ ([40, 72] : List Nat), Disj (memW s (globN s "bo" + k), 24) arr := by
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · have hd := List.pairwise_iff_getElem.1 hpw 3 4 (by omega) (by omega) (by omega)
      rw [harr] at hd
      simpa [hbo] using hd
    · have hd := List.pairwise_iff_getElem.1 hpw 4 5 (by omega) (by omega) (by omega)
      rw [harr] at hd
      simpa [hbo] using disj_symm hd
  have hbound := (ivl_allocated_bound hW.1.1.2 (bo_words hWT.2.2.1 hE.bo_nz).1).2
  apply txBacking_store hback hm
  · intro k hk he
    have ht := congrArg BitVec.toNat he
    have hk' : k = 40 ∨ k = 72 := by simpa using hk
    have hlt : globN s "bo" + k < 2 ^ 64 := by dsimp at hbound; omega
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at ht
    have hd := disj_of_inside_right hin hdbo
    unfold Disj at hd
    dsimp at hd
    omega
  · intro k hk he
    have ht := congrArg BitVec.toNat he
    have hlt : memW s (globN s "bo" + k) < 2 ^ 64 := by
      unfold memW
      split
      · exact BitVec.isLt _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at ht
    have hd := disj_of_inside_right hin (hdhead k hk)
    unfold Disj at hd
    dsimp at hd
    omega

/-- The concrete log-slot copy store retains both transaction backing facts. -/
theorem hoare_logSlot_store_txBacking :
    Hoare (fun s => Phase4LogSlotReady s ∧ TxBacking s)
      (.store (.var .local (ofString "slot")) phase4LogCopySrc)
      (fun r t => r = none → TxBacking t) := by
  refine R13Shards.Hoare.store_fall fun s x v mem' hp hx hv hst => ?_
  obtain ⟨w, rfl⟩ := phase4LogCopySrc_word s v hv
  obtain ⟨_, _, hm⟩ := R13Shards.panMemStoresHOL_word_spec
    (by simpa only [flattenHOL] using hst)
  have hlu : s.locals.lookup (ofString "slot") = some (.val (.word x)) := hx
  have hslot : locN s "slot" = x.toNat := by simp only [locN, hlu]
  apply txBacking_store_log_array hp.1.1.1.1.1.1 hp.2 _ hm
  simpa only [hslot] using hp.1.2.2

end PtxP34

namespace PtxP34
open PtxP1

/-- The typed log-copy guard and backing frame ignore temporary locals. -/
theorem localsOnly_phase4TypedLogPointers_backing :
    LocalsOnly ["index", "out", "logs", "rc", "nl", "lp"]
      (fun s => Phase4TypedLogPointers s ∧ TxBacking s) := by
  intro F s locals k hl hp
  exact ⟨localsOnly_phase4TypedLogPointers s locals k hl hp.1, hp.2⟩

/-- A backing-preserving push resume lifts through the concrete log-copy body. -/
theorem hoare_phase4LogCopyBody_backing
    (hresume : DecCallResumeOn (fun s => Phase4TypedLogPointers s ∧ TxBacking s)
      (fun s => (Phase4LogSlotReady s ∧
        (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
        ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p))) ∧ TxBacking s)
      (ofString "slot") (ofString "lst_push")
      [.load .one (.op .add [.var .global (ofString "bo"), .const 40]), .const 8]) :
    Hoare (fun s => Phase4TypedLogPointers s ∧ TxBacking s) phase4LogCopyBody
      (fun r t => r = none → Phase4TypedLogPointers t ∧ TxBacking t) := by
  apply Hoare.decCall_fall (R := fun s => (Phase4LogSlotReady s ∧
        (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
        ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p))) ∧ TxBacking s)
    (by decide) localsOnly_phase4TypedLogPointers_backing hresume
  apply Hoare.seq_fall (R := fun s => Phase4TypedLogPointers s ∧ TxBacking s)
  · exact ⟨fun s hc hp hnt hr =>
      ⟨(hoare_logSlot_store_typed phase4LogCopySrc phase4LogCopySrc_word).run s hc hp.1 hnt hr,
        hoare_logSlot_store_txBacking.run s hc ⟨hp.1.1, hp.2⟩ hnt hr⟩⟩
  · apply Hoare.assign
    · intro F s v hp _ _
      exact LocalsOnly.setVar localsOnly_phase4TypedLogPointers_backing (by decide) v s hp
    · intro F s _ hr
      cases hr

/-- The full log-copy loop retains backing given its push-resume contract. -/
theorem hoare_phase4LogCopyLoop_backing
    (hresume : DecCallResumeOn (fun s => Phase4TypedLogPointers s ∧ TxBacking s)
      (fun s => (Phase4LogSlotReady s ∧
        (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
        ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p))) ∧ TxBacking s)
      (ofString "slot") (ofString "lst_push")
      [.load .one (.op .add [.var .global (ofString "bo"), .const 40]), .const 8]) :
    Hoare (fun s => Phase4TypedLogPointers s ∧ TxBacking s)
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl")))
        phase4LogCopyBody)
      (fun r t => r = none → Phase4TypedLogPointers t ∧ TxBacking t) := by
  exact hoare_while_less_localsOnly localsOnly_phase4TypedLogPointers_backing _ _
    (hoare_phase4LogCopyBody_backing hresume)
    (by unfold phase4LogCopyBody; ptx_incr) (by decide)

end PtxP34

namespace PtxP34
open PtxP1

/-- The backing-aware log-copy loop satisfies the original concrete clock bound. -/
theorem phase4LogCopyLoop_backing_bound (h : PtxCallees)
    (hresume : DecCallResumeOn (fun s => Phase4TypedLogPointers s ∧ TxBacking s)
      (fun s => (Phase4LogSlotReady s ∧
        (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
        ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p))) ∧ TxBacking s)
      (ofString "slot") (ofString "lst_push")
      [.load .one (.op .add [.var .global (ofString "bo"), .const 40]), .const 8]) :
    TerminatingProgBoundedOn (fun s => Phase4TypedLogPointers s ∧ TxBacking s)
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl")))
        phase4LogCopyBody) ((2 ^ 64 + 1) * ((K.lst_push + 1) + 1)) := by
  apply while_less_localsOnly localsOnly_phase4TypedLogPointers_backing
  · have hb : TerminatingProgBoundedOn (fun s => Phase4TypedLogPointers s ∧ TxBacking s)
        phase4LogCopyBody (K.lst_push + (0 + 0) + 1) :=
      TerminatingProgBoundedOn.decCall_on h.fb_lst_push
        (ofString "slot") ShapeHOL.one
        [.load .one (.op .add [.var .global (ofString "bo"), .const 40]), .const 8]
        (Bc := 0 + 0)
        (continuation := .seq (.store (.var .local (ofString "slot")) phase4LogCopySrc)
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))
        (P := fun s => Phase4TypedLogPointers s ∧ TxBacking s)
        (Q := fun s => (Phase4LogSlotReady s ∧
          (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
          ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p))) ∧ TxBacking s)
        (by intro F s vs body callee ret hc hp ha hl
            exact guestInv_callEntry s callee hp.1.1.1.1.1.1.1.1.1)
        hresume
        (by
          intro F s hc hp
          exact seq_bound_trans
            (P := fun s => (Phase4LogSlotReady s ∧
              (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
              ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p))) ∧ TxBacking s)
            (Q := fun s => Phase4TypedLogPointers s ∧ TxBacking s)
            (fun t _ _ _ => by
              have ht := clock_store t (.var .local (ofString "slot")) phase4LogCopySrc
              exact ⟨by omega, by omega⟩)
            ⟨fun t ht hp hnt hr =>
              ⟨(hoare_logSlot_store_typed phase4LogCopySrc phase4LogCopySrc_word).run t ht hp.1 hnt hr,
                hoare_logSlot_store_txBacking.run t ht ⟨hp.1.1, hp.2⟩ hnt hr⟩⟩
            (fun t _ _ _ => by
              have ht := clock_assign t .local (ofString "i")
                (.op .add [.var .local (ofString "i"), .const 1])
              exact ⟨by omega, by omega⟩) s hc hp)
    intro F s hc hp
    simpa only [Nat.zero_add, Nat.add_zero] using hb s hc hp
  · exact hoare_phase4LogCopyBody_backing hresume
  · unfold phase4LogCopyBody
    ptx_incr

/-- Compose the backing-aware log loop with its stable-allocation continuation. -/
theorem phase4LogCopyLoop_backing_cut (h : PtxCallees)
    (hresume : DecCallResumeOn (fun s => Phase4TypedLogPointers s ∧ TxBacking s)
      (fun s => (Phase4LogSlotReady s ∧
        (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
        ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p))) ∧ TxBacking s)
      (ofString "slot") (ofString "lst_push")
      [.load .one (.op .add [.var .global (ofString "bo"), .const 40]), .const 8])
    {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn (fun s => Phase4TypedLogPointers s ∧ TxBacking s) tail b) :
    TerminatingProgBoundedOn (fun s => Phase4TypedLogPointers s ∧ TxBacking s)
      (spinePlug 1 (spineAt 129 ptxCode) tail)
      ((2 ^ 64 + 1) * ((K.lst_push + 1) + 1) + b) := by
  have hb := @seq_bound_trans _ _ _ _ _ _ (phase4LogCopyLoop_backing_bound h hresume)
    (hoare_phase4LogCopyLoop_backing hresume) htail
  unfold ptxCode
  intro F s hc hp
  exact hb s hc hp

end PtxP34

namespace PtxP34
open PtxP1

/-- Initializing the log-copy counter preserves the backing-aware typed guard. -/
theorem phase4LogCounter_backing_cut {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn (fun s => Phase4TypedLogPointers s ∧ TxBacking s) tail b) :
    TerminatingProgBoundedOn (fun s => Phase4TypedLogPointers s ∧ TxBacking s)
      (spinePlug 1 (spineAt 128 ptxCode) tail) b := by
  have hi : Hoare (fun s => Phase4TypedLogPointers s ∧ TxBacking s)
      (.assign .local (ofString "i") (.const 0))
      (fun r t => r = none → Phase4TypedLogPointers t ∧ TxBacking t) := by
    apply Hoare.assign
    · intro F s v hp _ _
      exact LocalsOnly.setVar localsOnly_phase4TypedLogPointers_backing (by decide) v s hp
    · intro F s _ hr
      cases hr
  unfold ptxCode
  intro F s hc hp
  rw [← Nat.zero_add b]
  refine seq_bound_trans ?_ hi htail s hc hp
  intro G t _ _ _
  have ht := clock_assign t .local (ofString "i") (.const 0)
  exact ⟨by omega, by omega⟩

/-- Compose counter initialization, log pushing, capacity setup and stable copying. -/
theorem phase4LogLoop_stable_backing_cut (h : PtxCallees)
    (hresume : DecCallResumeOn (fun s => Phase4TypedLogPointers s ∧ TxBacking s)
      (fun s => (Phase4LogSlotReady s ∧
        (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
        ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p))) ∧ TxBacking s)
      (ofString "slot") (ofString "lst_push")
      [.load .one (.op .add [.var .global (ofString "bo"), .const 40]), .const 8])
    {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn Phase4StableBackingReady tail b) :
    TerminatingProgBoundedOn (fun s => Phase4TypedLogPointers s ∧ TxBacking s)
      (spinePlug 9 (spineAt 128 ptxCode) tail)
      ((2 ^ 64 + 1) * ((K.lst_push + 1) + 1) + (K.lst_new + (2 ^ 28 + 1 + b) + 1)) := by
  have hb := @phase4LogCounter_backing_cut _ _
    (phase4LogCopyLoop_backing_cut h hresume
      (stable_capacity_setup_copy_backing_cut (stable_allocation_decl_loop_backing_cut h htail)))
  have he : spinePlug 9 (spineAt 128 ptxCode) tail =
      spinePlug 1 (spineAt 128 ptxCode)
        (spinePlug 1 (spineAt 129 ptxCode)
          (spinePlug 2 (spineAt 130 ptxCode) (spinePlug 5 (spineAt 132 ptxCode) tail))) := by
    unfold ptxCode
    rfl
  rw [he]
  intro F s hc hp
  exact hb s hc hp

end PtxP34

namespace PtxP34
open PtxP1

/-- Loading the source count and pointer retains both transaction backings. -/
theorem phase4LogPointers_backing_cut {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn (fun s => Phase4TypedLogPointers s ∧ TxBacking s) tail b) :
    TerminatingProgBoundedOn (fun s => Phase4ReceiptEncoded s ∧ TxBacking s)
      (spinePlug 2 (spineAt 126 ptxCode) tail) b := by
  unfold ptxCode
  refine dec_bound_trans (P := fun s => Phase4ReceiptEncoded s ∧ TxBacking s)
    (Q := fun s => (Phase4LogCountReady s ∧
      ∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧ TxBacking s)
    (fun s v hp he => ⟨phase4LogCount_load_typed s v hp.1 he, hp.2⟩) ?_
  intro F t hc ht
  refine dec_bound_trans (P := fun s => (Phase4LogCountReady s ∧
    ∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧ TxBacking s)
    ?_ htail t hc ht
  intro F s v hp he
  obtain ⟨hr, n, p, hn, hl⟩ := phase4LogPointer_load_typed s v hp.1.1 hp.1.2 he
  exact ⟨⟨hr, ⟨n, hn⟩, hr.1.2.2, ⟨p, hl⟩⟩, hp.2⟩

end PtxP34

namespace PtxP34
open PtxP1

/-- Receipt-array writes are separated from both transaction backing headers. -/
theorem txBacking_store_receipt_array {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hW : TxWorld s) (hback : TxBacking s) {x : BitVec 64}
    (hin : Inside (x.toNat, 8) (memW s (globN s "bo" + 32))
      (memW s (globN s "bo" + 32) + (16 * memW s (globN s "bo" + 80) + 16)))
    {mem' : BitVec 64 → HolWordLab 64} (hm : ∀ a, a ≠ x → mem' a = s.memory a) :
    TxBacking {s with memory := mem'} := by
  obtain ⟨S, hWT⟩ := hW.1.2
  have hE := hW.2
  obtain ⟨_, hpw, hsep, _, _⟩ := fixedObjects_disj_parts hWT.2.2.1
  obtain ⟨_, _, hbo⟩ := blockOutObjects_eq_list hE hWT.1
  let arr := (memW s (globN s "bo" + 32), 16 * memW s (globN s "bo" + 80) + 16)
  have hlen : (blockOutObjects s).length = 7 := by rw [hbo]; rfl
  have harr : (blockOutObjects s)[1]'(by omega) = arr := by simp [hbo, arr]
  have hmem : arr ∈ blockOutObjects s := harr ▸ List.getElem_mem (by omega : 1 < (blockOutObjects s).length)
  have hdbo : Disj (globN s "bo", 88) arr := by
    apply hsep _ (List.mem_map.2 ⟨("bo", 88), by decide, by simp [hE.bo_nz]⟩)
    exact List.mem_append_left _ (List.mem_append_right _ hmem)
  have hdhead : ∀ k ∈ ([40, 72] : List Nat), Disj (memW s (globN s "bo" + k), 24) arr := by
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · have hd := List.pairwise_iff_getElem.1 hpw 1 3 (by omega) (by omega) (by omega)
      rw [harr] at hd
      simpa [hbo] using disj_symm hd
    · have hd := List.pairwise_iff_getElem.1 hpw 1 5 (by omega) (by omega) (by omega)
      rw [harr] at hd
      simpa [hbo] using disj_symm hd
  have hbound := (ivl_allocated_bound hW.1.1.2 (bo_words hWT.2.2.1 hE.bo_nz).1).2
  apply txBacking_store hback hm
  · intro k hk he
    have ht := congrArg BitVec.toNat he
    have hk' : k = 40 ∨ k = 72 := by simpa using hk
    have hlt : globN s "bo" + k < 2 ^ 64 := by dsimp at hbound; omega
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at ht
    have hd := disj_of_inside_right hin hdbo
    unfold Disj at hd
    dsimp at hd
    omega
  · intro k hk he
    have ht := congrArg BitVec.toNat he
    have hlt : memW s (globN s "bo" + k) < 2 ^ 64 := by
      unfold memW
      split
      exact BitVec.isLt _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at ht
    have hd := disj_of_inside_right hin (hdhead k hk)
    unfold Disj at hd
    dsimp at hd
    omega

/-- Either encoded-receipt word store retains the full backing-aware guard. -/
theorem store_receiptSlot_backing (off : Bool) :
    Hoare (fun s => Phase4ReceiptEncoded s ∧ TxBacking s)
      (.store (receiptDst off) (.rfield (if off then 1 else 0) (.var .local (ofString "rc"))))
      (fun r t => r = none → Phase4ReceiptEncoded t ∧ TxBacking t) := by
  refine R13Shards.Hoare.store_fall fun s x v mem' hp hx hv hst => ?_
  obtain ⟨h, hb⟩ := hp
  obtain ⟨a, b, he, _⟩ := h.2.2.2
  have hvw : ∃ w : HolWordLab 64, v = .val w := by
    cases off <;> simp [evalAt, evalHOLExact, he] at hv <;> subst v
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  obtain ⟨w, rfl⟩ := hvw
  obtain ⟨hdom, _, hm⟩ := R13Shards.panMemStoresHOL_word_spec (by simpa only [flattenHOL] using hst)
  exact ⟨receiptEncoded_store h hdom (receiptDst_inside h.1 off hx) hm,
    txBacking_store_receipt_array h.1.1 hb (receiptDst_inside h.1 off hx) hm⟩

end PtxP34

namespace PtxP34
open PtxP1

/-- Both encoded-receipt stores compose without losing transaction backing. -/
theorem phase4ReceiptStores_backing_cut {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn (fun s => Phase4ReceiptEncoded s ∧ TxBacking s) tail b) :
    TerminatingProgBoundedOn (fun s => Phase4ReceiptEncoded s ∧ TxBacking s)
      (spinePlug 2 (spineAt 124 ptxCode) tail) b := by
  have hb : TerminatingProgBoundedOn (fun s => Phase4ReceiptEncoded s ∧ TxBacking s)
      (spinePlug 2 (spineAt 124 ptxCode) tail) (0 + (0 + b)) := by
    unfold ptxCode
    refine seq_bound_trans (P := fun s => Phase4ReceiptEncoded s ∧ TxBacking s)
      (by intro F s _ _ _; have hc := clock_store s (receiptDst false)
            (.rfield (if false then 1 else 0) (.var .local (ofString "rc"))); exact ⟨by omega, by omega⟩)
      (store_receiptSlot_backing false) ?_
    exact seq_bound_trans (P := fun s => Phase4ReceiptEncoded s ∧ TxBacking s)
      (by intro F s _ _ _; have hc := clock_store s (receiptDst true)
            (.rfield (if true then 1 else 0) (.var .local (ofString "rc"))); exact ⟨by omega, by omega⟩)
      (store_receiptSlot_backing true) htail
  intro F s hc hp
  simpa only [Nat.zero_add] using hb s hc hp

/-- The encoded-receipt suffix reaches stable-copy exit with backing retained. -/
theorem phase4Encoded_stable_backing_cut (h : PtxCallees)
    (hresume : DecCallResumeOn (fun s => Phase4TypedLogPointers s ∧ TxBacking s)
      (fun s => (Phase4LogSlotReady s ∧
        (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
        ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p))) ∧ TxBacking s)
      (ofString "slot") (ofString "lst_push")
      [.load .one (.op .add [.var .global (ofString "bo"), .const 40]), .const 8])
    {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn Phase4StableBackingReady tail b) :
    TerminatingProgBoundedOn (fun s => Phase4ReceiptEncoded s ∧ TxBacking s)
      (spinePlug 13 (spineAt 124 ptxCode) tail)
      ((2 ^ 64 + 1) * ((K.lst_push + 1) + 1) + (K.lst_new + (2 ^ 28 + 1 + b) + 1)) := by
  have hb := @phase4ReceiptStores_backing_cut _ _ (phase4LogPointers_backing_cut
    (phase4LogLoop_stable_backing_cut h hresume htail))
  have he : spinePlug 13 (spineAt 124 ptxCode) tail =
      spinePlug 2 (spineAt 124 ptxCode)
        (spinePlug 2 (spineAt 126 ptxCode) (spinePlug 9 (spineAt 128 ptxCode) tail)) := by
    unfold ptxCode
    rfl
  rw [he]
  intro F s hc hp
  exact hb s hc hp

end PtxP34

namespace PtxP34
open PtxP1

/-- Only preservation of the other list's data word remains to strengthen the
typed log-push resume: the concrete push already supplies active backing. -/
theorem resume_lst_push_typed_logSlot_backing_of_other_header (h : PtxCallees)
    (hother : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) vs body callee ret v post,
      s.code = originalRuntimeCode → (Phase4TypedLogPointers s ∧ TxBacking s) →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        [.load .one (.op .add [.var .global (ofString "bo"), .const 40]), .const 8] = some vs →
      lookupCodeHOLFinite s.code.lookup (ofString "lst_push") vs = some (body, callee, ret) →
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
        (some (.returned v), post) →
      memW post (memW s (globN s "bo" + 72)) = memW s (memW s (globN s "bo" + 72))) :
    DecCallResumeOn (fun s => Phase4TypedLogPointers s ∧ TxBacking s)
      (fun s => (Phase4LogSlotReady s ∧
        (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
        ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p))) ∧ TxBacking s)
      (ofString "slot") (ofString "lst_push")
      [.load .one (.op .add [.var .global (ofString "bo"), .const 40]), .const 8] := by
  intro F s vs body callee ret v post hc hp ha hl hr
  have hout := resume_lst_push_typed_logSlot_backing h s vs body callee ret v post hc hp ha hl hr
  refine ⟨hout, hout.1.2.1, ?_⟩
  have hW := hp.1.1.1.1.1.1
  have harg := lst_push_bo40_arg s vs body callee ret hc hW ha hl
  have hw := funSpec_at_lookup h.wk_lst_push s hc vs body callee ret hl harg.1
    (by rw [hr]; simp)
  rw [hr] at hw
  have hs := hw (Or.inl ⟨v, rfl⟩)
  have hbo : globN post "bo" = globN s "bo" :=
    R16Shards.globN_eq_of_lookup (hs.2.2.1 _ (by decide))
  have hm : memW post (globN s "bo" + 72) = memW s (globN s "bo" + 72) :=
    hs.2.2.2.1 ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])
      (by simp) hW.2.bo_nz 72 (by simp) (by intro i hi; cases hi)
  change memW post (memW post (globN post "bo" + 72)) ≠ 0
  rw [hbo, hm, hother s vs body callee ret v post hc hp ha hl hr]
  exact hp.2.2

end PtxP34

namespace PtxP34
open PtxP1

/-- The concrete length write preserves every other memory cell. -/
theorem hoare_lst_push_length_write_frame (l n a : BitVec 64) (w : HolWordLab 64)
    (hne : a ≠ l + 8) :
    Hoare (fun s => s.locals.lookup (ofString "l") = some (.val (.word l)) ∧
      s.locals.lookup (ofString "n") = some (.val (.word n)) ∧ s.memory a = w)
      (.store (.op .add [.var .local (ofString "l"), .const 8])
        (.op .add [.var .local (ofString "n"), .const 1]))
      (fun r post => r = none → post.memory a = w) := by
  apply R13Shards.Hoare.store_fall
  intro F s x v mem' hp hx hv hm
  obtain ⟨hl, hn, hw⟩ := hp
  have hd : evalAt s (.op .add [.var .local (ofString "l"), .const 8]) =
      some (.val (.word (l + 8))) := by
    simp [evalAt, evalHOLExact, evalListHOLExact, hl, valueIsWord, valueWord, wordOpHOL, wordOp]
  have hs : evalAt s (.op .add [.var .local (ofString "n"), .const 1]) =
      some (.val (.word (n + 1))) := by
    simp [evalAt, evalHOLExact, evalListHOLExact, hn, valueIsWord, valueWord, wordOpHOL, wordOp]
  rw [hd] at hx
  have he : x = l + 8 := by cases hx; rfl
  subst x
  rw [hs] at hv
  have he : v = .val (.word (n + 1)) := (Option.some.inj hv).symm
  subst v
  obtain ⟨_, _, hf⟩ := R13Shards.panMemStoresHOL_word_spec (by simpa only [flattenHOL] using hm)
  exact (hf a hne).trans hw

/-- The shared push tail changes only the active list's length cell. -/
theorem lst_push_tail_memory_frame {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (l n a : BitVec 64) (v : ValueHOL 64)
    (hc : s.code = originalRuntimeCode)
    (hl : s.locals.lookup (ofString "l") = some (.val (.word l)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (hne : a ≠ l + 8)
    (hr : evaluateHOLFiniteState s
      (.seq (.store (.op .add [.var .local (ofString "l"), .const 8])
        (.op .add [.var .local (ofString "n"), .const 1]))
        (.return (.op .add
          [.load .one (.op .add [.var .local (ofString "l"), .const 0]),
           .panop .mul [.var .local (ofString "n"), .var .local (ofString "esz")]]))) =
      (some (.returned v), post)) : post.memory a = s.memory a := by
  obtain ⟨mid, hs, _, _, ht⟩ := store_seq_returned hr
  have hm := (hoare_lst_push_length_write_frame l n a (s.memory a) hne).run s hc
    ⟨hl, hn, rfl⟩ (by rw [hs]; simp)
  rw [hs] at hm
  have hm' := hm rfl
  rw [evaluateHOLFiniteState_return] at ht
  split at ht
  · cases ht
  · split at ht
    · have he := (Prod.mk.inj ht).2
      subst post
      exact hm'
    · cases ht

end PtxP34

namespace PtxP34
open PtxP1

theorem store_word_memory_frame {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {dst src : ExpHOL 64} {x a : BitVec 64} {w : HolWordLab 64}
    (hc : s.code = originalRuntimeCode)
    (hd : evalAt s dst = some (.val (.word x)))
    (hv : evalAt s src = some (.val w)) (hne : a ≠ x)
    (hr : evaluateHOLFiniteState s (.store dst src) = (none, post)) :
    post.memory a = s.memory a := by
  have hh : Hoare (fun t => evalAt t dst = some (.val (.word x)) ∧
      evalAt t src = some (.val w) ∧ t.memory a = s.memory a)
      (.store dst src) (fun r t => r = none → t.memory a = s.memory a) := by
    apply R13Shards.Hoare.store_fall
    intro G t y v mem' hp hy hval hm
    rw [hp.1] at hy
    have he : y = x := by cases hy; rfl
    subst y
    rw [hp.2.1] at hval
    have he : v = .val w := (Option.some.inj hval).symm
    subst v
    obtain ⟨_, _, hf⟩ := R13Shards.panMemStoresHOL_word_spec (by simpa only [flattenHOL] using hm)
    exact (hf a hne).trans hp.2.2
  have hh' := hh.run s hc ⟨hd, hv, rfl⟩ (by rw [hr]; simp)
  rw [hr] at hh'
  exact hh' rfl

/-- Growth header updates and the shared return tail preserve all cells outside
the active header's three words. -/
theorem lst_push_growth_writes_memory_frame {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (l n cap np a : BitVec 64) (v : ValueHOL 64)
    (hc : s.code = originalRuntimeCode)
    (hl : s.locals.lookup (ofString "l") = some (.val (.word l)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (hcap : s.locals.lookup (ofString "cap") = some (.val (.word cap)))
    (hnp : s.locals.lookup (ofString "np") = some (.val (.word np)))
    (h0 : a ≠ l) (h8 : a ≠ l + 8) (h16 : a ≠ l + 16)
    (hr : evaluateHOLFiniteState s
      (.seq (.store (.op .add [.var .local (ofString "l"), .const 0])
          (.var .local (ofString "np")))
        (.seq (.store (.op .add [.var .local (ofString "l"), .const 16])
            (.panop .mul [.var .local (ofString "cap"), .const 2]))
          (.seq (.store (.op .add [.var .local (ofString "l"), .const 8])
              (.op .add [.var .local (ofString "n"), .const 1]))
            (.return (.op .add
              [.load .one (.op .add [.var .local (ofString "l"), .const 0]),
               .panop .mul [.var .local (ofString "n"), .var .local (ofString "esz")]]))))) =
      (some (.returned v), post)) : post.memory a = s.memory a := by
  obtain ⟨mid, hs, hloc, hcode, ht⟩ := store_seq_returned hr
  have hm : mid.memory a = s.memory a := store_word_memory_frame hc
    (by simp [evalAt, evalHOLExact, evalListHOLExact, hl, valueIsWord, valueWord, wordOpHOL, wordOp])
    (by exact hnp) h0 hs
  obtain ⟨last, hs2, hloc2, hcode2, ht2⟩ := store_seq_returned ht
  have hml : mid.locals.lookup (ofString "l") = some (.val (.word l)) := by rw [hloc]; exact hl
  have hmc : mid.locals.lookup (ofString "cap") = some (.val (.word cap)) := by rw [hloc]; exact hcap
  have hm2 : last.memory a = mid.memory a := store_word_memory_frame (w := .word (cap * 2)) (hcode.trans hc)
    (by simp [evalAt, evalHOLExact, evalListHOLExact, hml, valueIsWord, valueWord, wordOpHOL, wordOp])
    (by simp [evalAt, evalHOLExact, evalListHOLExact, hmc, valueIsWord, valueWord, panOpHOL]) h16 hs2
  exact (lst_push_tail_memory_frame last post l n a v (hcode2.trans (hcode.trans hc))
    (by rw [hloc2, hloc]; exact hl) (by rw [hloc2, hloc]; exact hn) h8 ht2).trans (hm2.trans hm)

end PtxP34

namespace PtxP34
open PtxP1

theorem txWorld_list_headers_disjoint {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hW : TxWorld s) :
    Disj (memW s (globN s "bo" + 40), 24) (memW s (globN s "bo" + 72), 24) := by
  obtain ⟨S, hWT⟩ := hW.1.2
  obtain ⟨_, hpw, _, _, _⟩ := fixedObjects_disj_parts hWT.2.2.1
  obtain ⟨_, _, hbo⟩ := blockOutObjects_eq_list hW.2 hWT.1
  have hlen : (blockOutObjects s).length = 7 := by rw [hbo]; rfl
  have hd := List.pairwise_iff_getElem.1 hpw 3 5 (by omega) (by omega) (by omega)
  simpa [hbo] using hd

/-- Spatial separation discharges the three modular-address side conditions
needed to frame the receipt header through the log push's header writes. -/
theorem txWorld_other_header_ne_push_writes {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hW : TxWorld s) :
    let l := BitVec.ofNat 64 (memW s (globN s "bo" + 40))
    let a := BitVec.ofNat 64 (memW s (globN s "bo" + 72))
    a ≠ l ∧ a ≠ l + 8 ∧ a ≠ l + 16 := by
  obtain ⟨S, hWT⟩ := hW.1.2
  have hE := hW.2
  have hm : (memW s (globN s "bo" + 40), 24) ∈ fixedObjects s := by
    unfold fixedObjects
    apply List.mem_append_left
    apply List.mem_append_right
    simp [blockOutObjects, hE.bo_nz, hE.bo40]
  have ha := ((hWT.2.2.1.1 _ hm).resolve_left (by simp)).1
  have hb := (ivl_allocated_bound hW.1.1.2 ha).2
  have ha64 : memW s (globN s "bo" + 72) < 2 ^ 64 := by
    unfold memW
    split
    exact BitVec.isLt _
  have hd := txWorld_list_headers_disjoint hW
  dsimp only
  have hne : ∀ k : Nat, k < 24 →
      BitVec.ofNat 64 (memW s (globN s "bo" + 72)) ≠
        BitVec.ofNat 64 (memW s (globN s "bo" + 40)) + BitVec.ofNat 64 k := by
    intro k hk he
    have he' := congrArg BitVec.toNat he
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at he'
    have hl : memW s (globN s "bo" + 40) < 2 ^ 64 := by dsimp at hb; omega
    have hkl : k < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt ha64, Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt hkl,
      Nat.mod_eq_of_lt (by dsimp at hb; omega)] at he'
    unfold Disj at hd
    dsimp at hd
    omega
  exact ⟨by simpa using hne 0 (by decide), hne 8 (by decide), hne 16 (by decide)⟩

end PtxP34

namespace PtxP34
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28

/-- A falling copy preserves a cell disjoint from its evaluated destination. -/
theorem memcpy_fall_memory_frame {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (args : List (ExpHOL 64)) (a : BitVec 64)
    (hc : s.code = originalRuntimeCode) (hG : GuestInv s)
    (hargs : ∀ vs,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some vs →
      ¬ CellHitsPos a.toNat
        (valWordNat (vs[0]?.getD (.rStruct [])), valWordNat (vs[2]?.getD (.rStruct []))))
    (hr : evaluateHOLFiniteState s (.call (some (none, none)) (ofString "memcpy") args) =
      (none, post)) : post.memory a = s.memory a := by
  have hf := funByteEff_memcpy
  obtain ⟨params, body, ret, hlook, hspec⟩ := hf
  rw [evaluateHOLFiniteState_call] at hr
  split at hr
  · simp at hr
  · split at hr
    · simp at hr
    · split at hr
      · simp at hr
      · rename_i optvs vs hv optbody body' callee ret' hl hz
        have hb := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "memcpy")
          params body body' ret ret' vs callee (by rw [hc]; exact hlook) hl
        subst body'
        have ht := lookupCodeHOLFinite_installed_return s (ofString "memcpy") params body body
          ret ret' vs callee (by rw [hc]; exact hlook) hl
        subst ret'
        rcases hs : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨r, done⟩
        rw [hs] at hr
        cases r with
        | none => simp at hr
        | some r =>
          cases r with
          | returned v =>
            dsimp only at hr
            split at hr
            · have hf := hspec (callEntryStateHOLFinite s callee) vs hc
                (guestInv_callEntry s callee hG) (by simpa [hc, callEntryStateHOLFinite] using hl)
                (by rw [hs]; simp) (by rw [hs]; exact Or.inl ⟨v, rfl⟩)
              rw [hs] at hf
              have hm : done.memory a = s.memory a := by
                by_contra hn
                obtain ⟨i, hi, hh⟩ := hf.cell_frame a hn
                simp only [List.mem_singleton] at hi
                subst i
                exact hargs vs hv hh
              cases hr
              exact hm
            · simp at hr
          | _ => simp at hr

/-- The concrete allocator changes no memory, including old list headers. -/
theorem alloc_return_memory {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64))
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (ret : ShapeHOL) (v : ValueHOL 64)
    (hc : s.code = originalRuntimeCode) (hA : ArenaReady s)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "alloc") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) : post.memory = s.memory := by
  have hb := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "alloc")
    [(ofString "n", .one)] (sourceFnBody Guest.Software.guestFn_alloc) body .one ret vs callee
    (by rw [hc]; exact R13Shards.lookup_alloc_r13) hl
  subst body
  have hp := R13Shards.alloc_body_resumes_props (callEntryStateHOLFinite s callee) hc
    ((arenaReady_with_locals s callee (s.clock - 1)).2 hA)
    (by rw [hr]; exact Or.inl ⟨v, rfl⟩)
  rw [hr] at hp
  obtain ⟨p, q, _, _, _, _, _, _, _, hm, _⟩ := hp
  exact hm

/-- A falling growth-store pair preserves every cell outside its two writes. -/
theorem lst_push_growth_stores_memory_frame {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (l cap np a : BitVec 64)
    (hc : s.code = originalRuntimeCode)
    (hl : s.locals.lookup (ofString "l") = some (.val (.word l)))
    (hcap : s.locals.lookup (ofString "cap") = some (.val (.word cap)))
    (hnp : s.locals.lookup (ofString "np") = some (.val (.word np)))
    (h0 : a ≠ l) (h16 : a ≠ l + 16)
    (hr : evaluateHOLFiniteState s
      (.seq (.store (.op .add [.var .local (ofString "l"), .const 0])
          (.var .local (ofString "np")))
        (.store (.op .add [.var .local (ofString "l"), .const 16])
          (.panop .mul [.var .local (ofString "cap"), .const 2]))) = (none, post)) :
    post.memory a = s.memory a := by
  rw [evaluateHOLFiniteState_seq_line780] at hr
  rcases hs : evaluateHOLFiniteState s
    (.store (.op .add [.var .local (ofString "l"), .const 0])
      (.var .local (ofString "np"))) with ⟨r, mid⟩
  rw [hs] at hr
  cases r with
  | some r => cases hr
  | none =>
    have hm : mid.memory a = s.memory a := store_word_memory_frame hc
      (by simp [evalAt, evalHOLExact, evalListHOLExact, hl, valueIsWord, valueWord, wordOpHOL, wordOp])
      (by exact hnp) h0 hs
    have hloc := store_fall_locals hs
    have hcode := (evaluateHOLFiniteState_metadata s
      (.store (.op .add [.var .local (ofString "l"), .const 0])
        (.var .local (ofString "np")))).1
    rw [hs] at hcode
    have hml : mid.locals.lookup (ofString "l") = some (.val (.word l)) := by rw [hloc]; exact hl
    have hmc : mid.locals.lookup (ofString "cap") = some (.val (.word cap)) := by rw [hloc]; exact hcap
    exact (store_word_memory_frame (w := .word (cap * 2)) (hcode.trans hc)
      (by simp [evalAt, evalHOLExact, evalListHOLExact, hml, valueIsWord, valueWord, wordOpHOL, wordOp])
      (by simp [evalAt, evalHOLExact, evalListHOLExact, hmc, valueIsWord, valueWord, panOpHOL])
      h16 hr).trans hm

/-- The concrete copy and growth stores frame an unrelated header cell. -/
theorem lst_push_copy_stores_memory_frame {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (l cap np a : BitVec 64)
    (hc : s.code = originalRuntimeCode) (hG : GuestInv s)
    (hl : s.locals.lookup (ofString "l") = some (.val (.word l)))
    (hcap : s.locals.lookup (ofString "cap") = some (.val (.word cap)))
    (hnp : s.locals.lookup (ofString "np") = some (.val (.word np)))
    (h0 : a ≠ l) (h16 : a ≠ l + 16)
    (hcopy : ∀ vs,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        [.var .local (ofString "np"),
         .load .one (.op .add [.var .local (ofString "l"), .const 0]),
         .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]] = some vs →
      ¬ CellHitsPos a.toNat
        (valWordNat (vs[0]?.getD (.rStruct [])), valWordNat (vs[2]?.getD (.rStruct []))))
    (hr : evaluateHOLFiniteState s
      (.seq (.call (some (none, none)) (ofString "memcpy")
        [.var .local (ofString "np"),
         .load .one (.op .add [.var .local (ofString "l"), .const 0]),
         .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]])
        (.seq (.store (.op .add [.var .local (ofString "l"), .const 0])
            (.var .local (ofString "np")))
          (.store (.op .add [.var .local (ofString "l"), .const 16])
            (.panop .mul [.var .local (ofString "cap"), .const 2])))) = (none, post)) :
    post.memory a = s.memory a := by
  rw [evaluateHOLFiniteState_seq_line780] at hr
  rcases hs : evaluateHOLFiniteState s
    (.call (some (none, none)) (ofString "memcpy")
      [.var .local (ofString "np"),
       .load .one (.op .add [.var .local (ofString "l"), .const 0]),
       .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]]) with ⟨r, mid⟩
  rw [hs] at hr
  cases r with
  | some r => cases hr
  | none =>
    obtain ⟨hlocal, hcode⟩ := ignored_call_fall_locals s mid _ _ hs
    exact (lst_push_growth_stores_memory_frame mid post l cap np a (hcode.trans hc)
      (by rw [hlocal]; exact hl) (by rw [hlocal]; exact hcap)
      (by rw [hlocal]; exact hnp) h0 h16 hr).trans
      (memcpy_fall_memory_frame s mid _ a hc hG hcopy hs)

/-- A fresh allocation's prefix cannot intersect any previously allocated cell. -/
theorem fresh_copy_not_hits {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {p size n : Nat} {a : BitVec 64}
    (hA : ArenaOK s) (hAp : ArenaOK post) (hf : FreshBlock s post p size)
    (ha : Allocated s (a.toNat, 8)) (hn : n ≤ (size + 7) / 8 * 8) :
    ¬ CellHitsPos a.toNat (p, n) := by
  have hd := hf.disj_allocated hA hAp ha
  unfold Disj at hd
  simp only [CellHitsPos, CellHits]
  dsimp at hd
  omega

/-- The whole allocating branch frames a cell when every successful allocator
return gives a copy destination disjoint from that cell. -/
theorem lst_push_alloc_branch_memory_frame (h : PtxCallees) {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (l cap a : BitVec 64)
    (hc : s.code = originalRuntimeCode) (hA : ArenaReady s)
    (hl : s.locals.lookup (ofString "l") = some (.val (.word l)))
    (hcap : s.locals.lookup (ofString "cap") = some (.val (.word cap)))
    (h0 : a ≠ l) (h16 : a ≠ l + 16)
    (hcopy : ∀ vs body callee ret (np : BitVec 64) allocated,
      lookupCodeHOLFinite s.code.lookup (ofString "alloc") vs = some (body, callee, ret) →
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
        (some (.returned (.val (.word np))), allocated) →
      ∀ args,
        evalListHOLFinite
          (setVarHOLFinite (ofString "np") (.val (.word np)) {allocated with locals := s.locals})
          (h := fun a => Classical.propDecidable (allocated.memaddrs a))
          [.var .local (ofString "np"),
           .load .one (.op .add [.var .local (ofString "l"), .const 0]),
           .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]] = some args →
        ¬ CellHitsPos a.toNat
          (valWordNat (args[0]?.getD (.rStruct [])), valWordNat (args[2]?.getD (.rStruct []))))
    (hr : evaluateHOLFiniteState s
      (.decCall (ofString "np") .one (ofString "alloc")
        [.panop .mul [.panop .mul
          [.var .local (ofString "esz"), .var .local (ofString "cap")], .const 2]]
        (.seq (.call (some (none, none)) (ofString "memcpy")
          [.var .local (ofString "np"),
           .load .one (.op .add [.var .local (ofString "l"), .const 0]),
           .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]])
          (.seq (.store (.op .add [.var .local (ofString "l"), .const 0])
              (.var .local (ofString "np")))
            (.store (.op .add [.var .local (ofString "l"), .const 16])
              (.panop .mul [.var .local (ofString "cap"), .const 2]))))) = (none, post)) :
    post.memory a = s.memory a := by
  obtain ⟨vs, body, callee, ret, rv, allocated, done, hlookup, hrun, hcont, hmem, _⟩ :=
    dec_call_fall_inv hr
  have hm := alloc_return_memory s allocated vs body callee ret rv hc hA hlookup hrun
  obtain ⟨np, rfl, _, hpost⟩ := alloc_return_nonzero h s vs body callee ret rv allocated hc
    ((arenaReady_with_locals s callee (s.clock - 1)).2 hA) hlookup hrun
  have hf := lst_push_copy_stores_memory_frame
    (setVarHOLFinite (ofString "np") (.val (.word np)) {allocated with locals := s.locals})
    done l cap np a hpost.1.code
    (guestInv_setVar _ _ _ ((arenaReady_with_locals allocated s.locals allocated.clock).2 hpost).1)
    (by simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "np" ≠ ofString "l" by decide] using hl)
    (by simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "np" ≠ ofString "cap" by decide] using hcap)
    (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
    h0 h16 (hcopy vs body callee ret np allocated hlookup hrun) hcont
  rw [hmem]
  exact hf.trans (congrFun hm a)

end PtxP34

namespace PtxP34
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28

/-- Retain evaluated arguments when exposing a falling declaration call. -/
theorem dec_call_fall_inv_args {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {x fname : MlS} {sh : ShapeHOL} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (h : evaluateHOLFiniteState s (.decCall x sh fname args cont) = (none, t)) :
    ∃ values body callee retShape rv post u,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values ∧
      lookupCodeHOLFinite s.code.lookup fname values = some (body, callee, retShape) ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned rv), post) ∧
      evaluateHOLFiniteState (setVarHOLFinite x rv {post with locals := s.locals}) cont = (none, u) ∧
      t.memory = u.memory := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · rename_i optvalues values hargs optbody body callee retShape hl
      split at h
      · simp at h
      · dsimp only at h
        rcases hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨r, post⟩
        rw [hr] at h
        cases r with
        | none => simp at h
        | some r =>
          cases r with
          | returned rv =>
            dsimp only at h
            split at h
            · rcases ht : evaluateHOLFiniteState
                (setVarHOLFinite x rv {post with locals := s.locals}) cont with ⟨rc, u⟩
              rw [ht] at h
              cases rc with
              | none =>
                have he := (Prod.mk.inj h).2
                exact ⟨_, body, callee, retShape, rv, post, u, hargs, hl, hr, ht,
                  congrArg (fun st => st.memory) he.symm⟩
              | some r => simp at h
            · simp at h
          | _ => simp at h

/-- The actual allocator arguments bound the subsequent copy within fresh memory. -/
theorem alloc_copy_header_disjoint (h : PtxCallees) {F : Type}
    (s allocated : PanSemStateFiniteExact 64 F) (n cap esz np a : BitVec 64)
    (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (hc : s.code = originalRuntimeCode) (hA : ArenaReady s)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (hcap : s.locals.lookup (ofString "cap") = some (.val (.word cap)))
    (hesz : s.locals.lookup (ofString "esz") = some (.val (.word esz)))
    (hle : n.toNat ≤ cap.toNat)
    (hbound : esz.toNat * cap.toNat * 2 < 2 ^ 64)
    (ha : Allocated s (a.toNat, 8))
    (hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.panop .mul [.panop .mul
        [.var .local (ofString "esz"), .var .local (ofString "cap")], .const 2]] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "alloc") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned (.val (.word np))), allocated)) :
    ∀ args,
      evalListHOLFinite
        (setVarHOLFinite (ofString "np") (.val (.word np)) {allocated with locals := s.locals})
        (h := fun a => Classical.propDecidable (allocated.memaddrs a))
        [.var .local (ofString "np"),
         .load .one (.op .add [.var .local (ofString "l"), .const 0]),
         .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]] = some args →
      ¬ CellHitsPos a.toNat
        (valWordNat (args[0]?.getD (.rStruct [])), valWordNat (args[2]?.getD (.rStruct []))) := by
  have hv : vs = [.val (.word (esz * cap * 2))] := by
    simpa [evalListHOLFinite, evalListHOLExact, evalHOLExact, hesz, hcap,
      valueIsWord, valueWord, panOpHOL] using hargs.symm
  subst vs
  have hlookup := hl
  rw [hc] at hlookup
  have hb := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "alloc")
    [(ofString "n", .one)] (sourceFnBody Guest.Software.guestFn_alloc) body .one ret _ callee
    (by rw [hc]; exact R13Shards.lookup_alloc_r13) hl
  subst body
  have ht := lookupCodeHOLFinite_installed_return s (ofString "alloc") [(ofString "n", .one)]
    (sourceFnBody Guest.Software.guestFn_alloc) (sourceFnBody Guest.Software.guestFn_alloc)
    .one ret _ callee (by rw [hc]; exact R13Shards.lookup_alloc_r13) hl
  subst ret
  obtain ⟨w, he, hnentry⟩ := R13Shards.lookupCode_one_word R13Shards.lookup_alloc_r13 hlookup
  have hw : w = esz * cap * 2 := by simpa using he.symm
  subst w
  have hspec := PtxP1.funSpec_at_lookup h.rt_alloc s hc _ _ callee _ hl
    ((arenaReady_with_locals s callee (s.clock - 1)).2 hA) (by rw [hr]; simp)
  rw [hr] at hspec
  obtain ⟨p, hp, hAp, _, hf⟩ := hspec _ rfl
  have hp' : p = np := by simpa using hp.symm
  subst p
  have heq : locN (callEntryStateHOLFinite s callee) "n" = esz.toNat * cap.toNat * 2 := by
    simp only [locN, callEntryStateHOLFinite, hnentry]
    have hb : esz.toNat * cap.toNat < 2 ^ 64 := by omega
    simp only [BitVec.toNat_mul]
    rw [Nat.mod_eq_of_lt hb]
    exact Nat.mod_eq_of_lt hbound
  rw [heq] at hf
  have hmul : (esz * n).toNat ≤ esz.toNat * cap.toNat * 2 := by
    have hh := Nat.mul_le_mul_left esz.toNat hle
    have hb : esz.toNat * n.toNat < 2 ^ 64 := by omega
    rw [BitVec.toNat_mul, Nat.mod_eq_of_lt hb]
    omega
  intro args he
  simp [evalListHOLFinite, evalListHOLExact, evalHOLExact,
    setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
    show ofString "np" ≠ ofString "esz" by decide,
    show ofString "np" ≠ ofString "n" by decide,
    show ofString "np" ≠ ofString "l" by decide,
    hesz, hn, valueIsWord, valueWord, panOpHOL] at he
  split at he
  · rename_i value values hv hvalues
    split at hvalues
    · rename_i src rest hsrc hrest
      have hrst : rest = [.val (.word (esz * n))] := by simpa using hrest.symm
      subst rest
      simp only [Option.some.injEq] at hvalues
      subst values
      have hv' : value = .val (.word np) := Option.some.inj hv.symm
      subst value
      have he' := Option.some.inj he
      subst args
      change ¬ CellHitsPos a.toNat (np.toNat, (esz * n).toNat)
      apply fresh_copy_not_hits hA.2 hAp.2 hf ha
      have hround : esz.toNat * cap.toNat * 2 ≤ (esz.toNat * cap.toNat * 2 + 7) / 8 * 8 := by omega
      exact hmul.trans hround
    · cases hvalues
  · cases he

/-- Growth preserves an allocated cell outside the active header, with the
copy separation discharged from the list length and capacity bounds. -/
theorem lst_push_alloc_branch_allocated_frame (h : PtxCallees) {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (l n cap esz a : BitVec 64)
    (hc : s.code = originalRuntimeCode) (hA : ArenaReady s)
    (hl : s.locals.lookup (ofString "l") = some (.val (.word l)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (hcap : s.locals.lookup (ofString "cap") = some (.val (.word cap)))
    (hesz : s.locals.lookup (ofString "esz") = some (.val (.word esz)))
    (hle : n.toNat ≤ cap.toNat) (hbound : esz.toNat * cap.toNat * 2 < 2 ^ 64)
    (ha : Allocated s (a.toNat, 8)) (h0 : a ≠ l) (h16 : a ≠ l + 16)
    (hr : evaluateHOLFiniteState s
      (.decCall (ofString "np") .one (ofString "alloc")
        [.panop .mul [.panop .mul
          [.var .local (ofString "esz"), .var .local (ofString "cap")], .const 2]]
        (.seq (.call (some (none, none)) (ofString "memcpy")
          [.var .local (ofString "np"),
           .load .one (.op .add [.var .local (ofString "l"), .const 0]),
           .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]])
          (.seq (.store (.op .add [.var .local (ofString "l"), .const 0])
              (.var .local (ofString "np")))
            (.store (.op .add [.var .local (ofString "l"), .const 16])
              (.panop .mul [.var .local (ofString "cap"), .const 2]))))) = (none, post)) :
    post.memory a = s.memory a := by
  obtain ⟨vs, body, callee, ret, rv, allocated, done, hargs, hlookup, hrun, hcont, hmem⟩ :=
    dec_call_fall_inv_args hr
  have hm := alloc_return_memory s allocated vs body callee ret rv hc hA hlookup hrun
  obtain ⟨np, rfl, _, hpost⟩ := alloc_return_nonzero h s vs body callee ret rv allocated hc
    ((arenaReady_with_locals s callee (s.clock - 1)).2 hA) hlookup hrun
  have hf := lst_push_copy_stores_memory_frame
    (setVarHOLFinite (ofString "np") (.val (.word np)) {allocated with locals := s.locals})
    done l cap np a hpost.1.code
    (guestInv_setVar _ _ _ ((arenaReady_with_locals allocated s.locals allocated.clock).2 hpost).1)
    (by simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "np" ≠ ofString "l" by decide] using hl)
    (by simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "np" ≠ ofString "cap" by decide] using hcap)
    (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]) h0 h16
    (alloc_copy_header_disjoint h s allocated n cap esz np a vs body callee ret
      hc hA hn hcap hesz hle hbound ha hargs hlookup hrun) hcont
  rw [hmem]
  exact hf.trans (congrFun hm a)

end PtxP34

namespace PtxP34

/-- Both capacity branches and the common length/return tail frame an old cell. -/
theorem lst_push_capacity_tail_memory_frame (h : PtxCallees) {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (l n cap esz a : BitVec 64) (v : ValueHOL 64)
    (hc : s.code = originalRuntimeCode) (hA : ArenaReady s)
    (hl : s.locals.lookup (ofString "l") = some (.val (.word l)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (hcap : s.locals.lookup (ofString "cap") = some (.val (.word cap)))
    (hesz : s.locals.lookup (ofString "esz") = some (.val (.word esz)))
    (hle : n.toNat ≤ cap.toNat) (hbound : esz.toNat * cap.toNat * 2 < 2 ^ 64)
    (ha : Allocated s (a.toNat, 8)) (h0 : a ≠ l) (h8 : a ≠ l + 8) (h16 : a ≠ l + 16)
    (hr : evaluateHOLFiniteState s
      (.seq
        (.ite (.cmp .notLower (.var .local (ofString "n")) (.var .local (ofString "cap")))
          (.decCall (ofString "np") .one (ofString "alloc")
            [.panop .mul [.panop .mul
              [.var .local (ofString "esz"), .var .local (ofString "cap")], .const 2]]
            (.seq
              (.call (some (none, none)) (ofString "memcpy")
                [.var .local (ofString "np"),
                 .load .one (.op .add [.var .local (ofString "l"), .const 0]),
                 .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]])
              (.seq
                (.store (.op .add [.var .local (ofString "l"), .const 0])
                  (.var .local (ofString "np")))
                (.store (.op .add [.var .local (ofString "l"), .const 16])
                  (.panop .mul [.var .local (ofString "cap"), .const 2]))))) .skip)
        (.seq (.store (.op .add [.var .local (ofString "l"), .const 8])
          (.op .add [.var .local (ofString "n"), .const 1]))
          (.return (.op .add
            [.load .one (.op .add [.var .local (ofString "l"), .const 0]),
             .panop .mul [.var .local (ofString "n"), .var .local (ofString "esz")]])))) =
      (some (.returned v), post)) : post.memory a = s.memory a := by
  obtain ⟨mid, hm, ht⟩ := seq_returned_of_not_returned (by
    apply ite_not_returned
    · apply dec_call_not_returned
      intro t
      apply seq_not_returned
      · exact ignored_call_not_returned _ _ _ _
      · intro t
        apply seq_not_returned
        · exact store_not_returned _ _ _ _
        · intro t; exact store_not_returned _ _ _ _
    · simp [evaluateHOLFiniteState_skip]) hr
  rcases ite_skip_fall_inv hm with hg | rfl
  · have hf := lst_push_alloc_branch_allocated_frame h s mid l n cap esz a
      hc hA hl hn hcap hesz hle hbound ha h0 h16 hg
    have hloc := lst_push_alloc_branch_lookup s mid _ hg
    have hmeta : ∀ p, evaluateHOLFiniteState s p = (none, mid) → mid.code = s.code := by
      intro p hp
      have hm := (evaluateHOLFiniteState_metadata s p).1
      rw [hp] at hm
      exact hm
    have hcode := hmeta _ hg
    exact (lst_push_tail_memory_frame mid post l n a v (hcode.trans hc)
      ((hloc _ (by decide)).trans hl) ((hloc _ (by decide)).trans hn) h8 ht).trans hf
  · exact lst_push_tail_memory_frame mid post l n a v hc hl hn h8 ht

/-- Expose the initializer value as well as memory-preserving scope restoration. -/
theorem dec_word_returned_inv_eval {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {x : MlS} {e : ExpHOL 64} {cont : ProgHOL 64} {v : ValueHOL 64}
    (hr : evaluateHOLFiniteState s (.dec x .one e cont) = (some (.returned v), post)) :
    ∃ w : BitVec 64, ∃ mid,
      evalAt s e = some (.val (.word w)) ∧
      evaluateHOLFiniteState (setVarHOLFinite x (.val (.word w)) s) cont =
        (some (.returned v), mid) ∧ post.memory = mid.memory := by
  rw [evaluateHOLFiniteState_dec_total] at hr
  dsimp only at hr
  split at hr
  · cases hr
  · rename_i value he
    split at hr
    · rename_i hshape
      have hw : ∃ w : BitVec 64, value = .val (.word w) := by
        cases value with
        | val z => cases z with
          | word w => exact ⟨w, rfl⟩
        | _ => simp [shapeOfHOLExact, shapeEqHOL] at hshape
      obtain ⟨w, rfl⟩ := hw
      rcases hb : evaluateHOLFiniteState (setVarHOLFinite x (.val (.word w)) s) cont with ⟨r, mid⟩
      rw [hb] at hr
      exact ⟨w, mid, he, by rw [← (Prod.mk.inj hr).1]; exact hb,
        congrArg (fun t => t.memory) (Prod.mk.inj hr).2.symm⟩
    · cases hr

theorem loaded_header_word_nat {F : Type} {s : PanSemStateFiniteExact 64 F}
    {l w : BitVec 64} {k : Nat}
    (hl : s.locals.lookup (ofString "l") = some (.val (.word l)))
    (hb : l.toNat + k < 2 ^ 64)
    (he : evalAt s (.load .one (.op .add [.var .local (ofString "l"), .const (BitVec.ofNat 64 k)])) =
      some (.val (.word w))) : w.toNat = memW s (l.toNat + k) := by
  have haddr : l + BitVec.ofNat 64 k = BitVec.ofNat 64 (l.toNat + k) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    have hk : k < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt hk]
  simp [evalAt, evalHOLExact, evalListHOLExact, hl, valueIsWord, valueWord, wordOpHOL, wordOp,
    haddr, memLoadHOLExact] at he
  simp [memW, he.2]

/-- The complete concrete push frames an allocated cell outside its header. -/
theorem lst_push_body_memory_frame (h : PtxCallees) {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (l esz a : BitVec 64) (v : ValueHOL 64)
    (hc : s.code = originalRuntimeCode) (hA : ArenaReady s)
    (hl : s.locals.lookup (ofString "l") = some (.val (.word l)))
    (hesz : s.locals.lookup (ofString "esz") = some (.val (.word esz)))
    (hlb : l.toNat + 24 ≤ 2 ^ 64)
    (hlen : memW s (l.toNat + 8) ≤ memW s (l.toNat + 16))
    (hbound : esz.toNat * memW s (l.toNat + 16) * 2 < 2 ^ 64)
    (ha : Allocated s (a.toNat, 8)) (h0 : a ≠ l) (h8 : a ≠ l + 8) (h16 : a ≠ l + 16)
    (hr : evaluateHOLFiniteState s (sourceFunctionEntry Guest.Software.guestFn_lst_push).2.2.1 =
      (some (.returned v), post)) : post.memory a = s.memory a := by
  dsimp only [sourceFunctionEntry, Guest.Software.guestFn_lst_push,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map] at hr
  obtain ⟨n, mid, hen, hr, hm⟩ := dec_word_returned_inv_eval hr
  obtain ⟨cap, last, hec, hr, hm'⟩ := dec_word_returned_inv_eval hr
  have hnval := loaded_header_word_nat hl (by omega : l.toNat + 8 < 2 ^ 64) hen
  have hcl : (setVarHOLFinite (ofString "n") (.val (.word n)) s).locals.lookup (ofString "l") =
      some (.val (.word l)) := by
    simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "n" ≠ ofString "l" by decide] using hl
  have hcval := loaded_header_word_nat hcl (by omega : l.toNat + 16 < 2 ^ 64) hec
  change cap.toNat = memW s (l.toNat + 16) at hcval
  have hf := lst_push_capacity_tail_memory_frame h
    (setVarHOLFinite (ofString "cap") (.val (.word cap))
      (setVarHOLFinite (ofString "n") (.val (.word n)) s)) last l n cap esz a v hc
    ((arenaReady_with_locals s _ s.clock).2 hA)
    (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl,
      show ofString "cap" ≠ ofString "l" by decide, show ofString "n" ≠ ofString "l" by decide])
    (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "cap" ≠ ofString "n" by decide])
    (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
    (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hesz,
      show ofString "cap" ≠ ofString "esz" by decide, show ofString "n" ≠ ofString "esz" by decide])
    (by rw [hnval, hcval]; exact hlen) (by rw [hcval]; exact hbound) ha h0 h8 h16 hr
  rw [hm, hm']
  exact hf

end PtxP34

namespace PtxP34

/-- Transaction typing bounds the active capacity and allocates the other header. -/
theorem txWorld_log_push_frame_bounds {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hW : TxWorld s) (hback : TxBacking s) :
    let l := memW s (globN s "bo" + 40)
    let a := memW s (globN s "bo" + 72)
    l + 24 ≤ 2 ^ 64 ∧ memW s (l + 8) ≤ memW s (l + 16) ∧
      8 * memW s (l + 16) * 2 < 2 ^ 64 ∧ Allocated s (a, 8) := by
  obtain ⟨S, hWT⟩ := hW.1.2
  have hE := hW.2
  have hok := hWT.1.2.2.2.2.2.2.2.2.2.2.1 hE.bo_nz 40 (by simp) hE.bo40
  have hpositive := hok.1
  have hheaders : ∀ k ∈ ([40, 72] : List Nat),
      Allocated s (memW s (globN s "bo" + k), 24) := by
    intro k hk
    apply ((hWT.2.2.1.1 _ ?_).resolve_left (by simp)).1
    unfold fixedObjects
    apply List.mem_append_left
    apply List.mem_append_right
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · simp [blockOutObjects, hE.bo_nz, hE.bo40]
    · simp [blockOutObjects, hE.bo_nz, hE.bo72]
  have harr : (memW s (memW s (globN s "bo" + 40)),
      8 * memW s (memW s (globN s "bo" + 40) + 16)) ∈ fixedObjects s := by
    unfold fixedObjects
    apply List.mem_append_left
    apply List.mem_append_right
    simp [blockOutObjects, hE.bo_nz, hE.bo40, hback.1,
      show memW s (memW s (globN s "bo" + 40) + 16) ≠ 0 by omega]
  have halloc := ((hWT.2.2.1.1 _ harr).resolve_left (by dsimp; omega)).1
  have hsmall : 8 * memW s (memW s (globN s "bo" + 40) + 16) ≤ heapEnd := by
    rcases halloc with hi | hi
    · have := hW.1.1.2.2.1
      have hh : heapLimit ≤ heapEnd := by decide
      dsimp [Inside] at hi
      omega
    · dsimp [Inside] at hi
      have hs : scratchEnd ≤ heapEnd := by decide
      omega
  refine ⟨(ivl_allocated_bound hW.1.1.2 (hheaders 40 (by simp))).2, hok.2, ?_, ?_⟩
  · have hh : heapEnd * 2 < 2 ^ 64 := by decide
    omega
  · rcases hheaders 72 (by simp) with hi | hi
    · left; unfold Inside at *; dsimp at *; omega
    · right; unfold Inside at *; dsimp at *; omega

/-- The concrete block-log push preserves the receipt-list data word. -/
theorem lst_push_bo40_other_header (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hW : TxWorld s) (hback : TxBacking s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.load .one (.op .add [.var .global (ofString "bo"), .const 40]), .const 8] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "lst_push") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    memW post (memW s (globN s "bo" + 72)) = memW s (memW s (globN s "bo" + 72)) := by
  have harg := lst_push_bo40_arg s vs body callee ret hc hW ha hl
  have hbody := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "lst_push")
    [(ofString "l", .one), (ofString "esz", .one)] _ body .one ret vs callee
    (by rw [hc]; exact R13Shards.lookup_lst_push) hl
  subst body
  have hret := lookupCodeHOLFinite_installed_return s (ofString "lst_push")
    [(ofString "l", .one), (ofString "esz", .one)] _ _ .one ret vs callee
    (by rw [hc]; exact R13Shards.lookup_lst_push) hl
  subst ret
  have hl' := hl
  rw [hc] at hl'
  obtain ⟨l, esz, _, hloc, hesz⟩ := R13Shards.lookupCode_two_words (by decide) R13Shards.lookup_lst_push hl'
  have hln : l.toNat = memW s (globN s "bo" + 40) := by
    simpa only [locN, callEntryStateHOLFinite, hloc] using harg.2
  have hen : esz.toNat = 8 := by
    simpa only [locN, callEntryStateHOLFinite, hesz] using harg.1.2.2.2
  have hlbv : l = BitVec.ofNat 64 (memW s (globN s "bo" + 40)) := by
    simp [← hln]
  let a := BitVec.ofNat 64 (memW s (globN s "bo" + 72))
  have han : a.toNat = memW s (globN s "bo" + 72) := by
    unfold a memW
    split
    simp
  obtain ⟨hb, hn, hcap, haa⟩ := txWorld_log_push_frame_bounds hW hback
  obtain ⟨h0, h8, h16⟩ := txWorld_other_header_ne_push_writes hW
  have hf := lst_push_body_memory_frame h (callEntryStateHOLFinite s callee) post l esz a v hc
    harg.1.1.1 hloc hesz (by simpa [hln] using hb)
    (by simpa only [callEntryStateHOLFinite, memW, hln] using hn)
    (by simpa only [callEntryStateHOLFinite, memW, hln, hen] using hcap)
    (by change Allocated s (a.toNat, 8); rw [han]; exact haa)
    (by simpa only [hlbv] using h0) (by simpa only [hlbv] using h8)
    (by simpa only [hlbv] using h16) hr
  change (match post.memory a with | .word w => w.toNat) =
    (match s.memory a with | .word w => w.toNat)
  rw [hf]
  rfl

/-- The log-push resume now preserves both backing pointers without an extra
other-header preservation hypothesis. -/
theorem resume_lst_push_typed_logSlot_txBacking (h : PtxCallees) :
    DecCallResumeOn (fun s => Phase4TypedLogPointers s ∧ TxBacking s)
      (fun s => (Phase4LogSlotReady s ∧
        (∃ n : BitVec 64, s.locals.lookup (ofString "nl") = some (.val (.word n))) ∧
        ∃ p : BitVec 64, s.locals.lookup (ofString "lp") = some (.val (.word p))) ∧ TxBacking s)
      (ofString "slot") (ofString "lst_push")
      [.load .one (.op .add [.var .global (ofString "bo"), .const 40]), .const 8] := by
  apply resume_lst_push_typed_logSlot_backing_of_other_header h
  intro F s vs body callee ret v post hc hp ha hl hr
  exact lst_push_bo40_other_header h s vs body callee ret v post hc
    hp.1.1.1.1.1.1 hp.2 ha hl hr

/-- The encoded-receipt suffix retains backing through concrete log pushes
and the stable-log copy, with no additional push-resume premise. -/
theorem phase4Encoded_stable_txBacking_cut (h : PtxCallees)
    {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn Phase4StableBackingReady tail b) :
    TerminatingProgBoundedOn (fun s => Phase4ReceiptEncoded s ∧ TxBacking s)
      (spinePlug 13 (spineAt 124 ptxCode) tail)
      ((2 ^ 64 + 1) * ((K.lst_push + 1) + 1) + (K.lst_new + (2 ^ 28 + 1 + b) + 1)) := by
  exact phase4Encoded_stable_backing_cut h
    (resume_lst_push_typed_logSlot_txBacking h) htail

end PtxP34

namespace PtxP34

/-- Framing the nonempty fixed objects suffices to retain both backing pointers. -/
theorem txBacking_of_fixed_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hW : TxWorld s) (hb : TxBacking s)
    (hbo : globN post "bo" = globN s "bo")
    (hu : ∀ i ∈ fixedObjects s, i.2 ≠ 0 → IvlUnhit s post i) :
    TxBacking post := by
  obtain ⟨S, hWT⟩ := hW.1.2
  have hE := hW.2
  have hbw := bo_words hWT.2.2.1 hE.bo_nz
  have hbf : (globN s "bo", 88) ∈ fixedObjects s := by
    unfold fixedObjects
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_map.mpr
    exact ⟨("bo", 88), by decide, by simp [hE.bo_nz]⟩
  have hlf : ∀ k ∈ ([40, 72] : List Nat),
      (memW s (globN s "bo" + k), 24) ∈ fixedObjects s := by
    intro k hk
    unfold fixedObjects
    apply List.mem_append_left
    apply List.mem_append_right
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · simp [blockOutObjects, hE.bo_nz, hE.bo40]
    · simp [blockOutObjects, hE.bo_nz, hE.bo72]
  have hlt : ∀ k ∈ ([40, 72] : List Nat),
      Allocated s (memW s (globN s "bo" + k), 24) ∧
      WordsOK s (memW s (globN s "bo" + k), 24) := by
    intro k hk
    exact (hWT.2.2.1.1 _ (hlf k hk)).resolve_left (by simp)
  exact txBacking_of_unhit_headers hb hbo hbw.2.1
    (ivl_allocated_bound hW.1.1.2 hbw.1).2 (hu _ hbf (by simp))
    (fun k hk => (hlt k hk).2.1)
    (fun k hk => (ivl_allocated_bound hW.1.1.2 (hlt k hk).1).2)
    (fun k hk => hu _ (hlf k hk) (by simp))

end PtxP34

namespace PtxP34
open PtxP1

/-- Receipt encoding threads backing once its callee memory contract is supplied. -/
theorem phase4EncodeReceipt_backing_cut (h : PtxCallees)
    (hkeep : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) vs body callee ret v post,
      s.code = originalRuntimeCode → Phase4ReceiptReady s → TxBacking s →
      lookupCodeHOLFinite s.code.lookup (ofString "encode_receipt") vs = some (body, callee, ret) →
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post) →
      locN (callEntryStateHOLFinite s callee) "logs" = locN s "logs" → TxBacking post)
    {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn (fun s => Phase4ReceiptEncoded s ∧ TxBacking s) tail b) :
    TerminatingProgBoundedOn (fun s => Phase4ReceiptReady s ∧ TxBacking s)
      (spinePlug 1 (spineAt 123 ptxCode) tail) (K.encode_receipt + b + 1) := by
  unfold ptxCode
  refine @TerminatingProgBoundedOn.decCall_on
    (fun s => Phase4ReceiptReady s ∧ TxBacking s) GuestInv
    (fun s => Phase4ReceiptEncoded s ∧ TxBacking s) _ _ _
    h.fb_encode_receipt _ _ _ _ ?_ ?_ htail
  · intro F s vs body callee ret hc hp ha hl
    exact guestInv_callEntry s callee hp.1.1.1.1.1.1
  · intro F s vs body callee ret v post hc hp ha hl hr
    have hg := encode_receipt_logs_param s _ _ _ vs body callee ret hc ha hl
    refine ⟨encode_receipt_encoded_resume h s vs body callee ret v post hc hl hr hp.1 hg, ?_⟩
    exact hkeep s vs body callee ret v post hc hp.1 hp.2 hl hr hg

/-- The remaining Phase-4 prefix contracts are credit and receipt encoding;
log pushes and stable copying are discharged concretely. -/
theorem phase4BackingPrefix_of_credit_encode (h : PtxCallees)
    (hcredit : ∀ args : List (ExpHOL 64), Hoare TxAfterCallBackingStrong
      (.call (some (none, none)) (ofString "create_ether") args)
      (fun r t => r = none → TxAfterCallBackingStrong t))
    (hkeep : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) vs body callee ret v post,
      s.code = originalRuntimeCode → Phase4ReceiptReady s → TxBacking s →
      lookupCodeHOLFinite s.code.lookup (ofString "encode_receipt") vs = some (body, callee, ret) →
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post) →
      locN (callEntryStateHOLFinite s callee) "logs" = locN s "logs" → TxBacking post) :
    Phase4BackingPrefix := by
  intro tail b ht
  have hb := @phase4BeforeReceipt_backing_cut h hcredit _ _
    (phase4EncodeReceipt_backing_cut h hkeep (phase4Encoded_stable_txBacking_cut h ht))
  have he : spinePlug 38 (spineAt 99 ptxCode) tail =
      spinePlug 24 (spineAt 99 ptxCode)
        (spinePlug 1 (spineAt 123 ptxCode) (spinePlug 13 (spineAt 124 ptxCode) tail)) := by
    unfold ptxCode
    rfl
  rw [he]
  intro F s hc hp
  exact hb s hc hp.1

end PtxP34

namespace PtxP34
open PtxP1

/-- A concrete frame outside old allocated headers retains both backing words.
The write regions may contain byte-sized scratch buffers. -/
theorem txBacking_of_allocated_frame {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {R : List Ivl}
    (hW : TxWorld s) (hb : TxBacking s) (hAp : ArenaOK post)
    (hgrow : AllocatorGrows s post)
    (hbo : globN post "bo" = globN s "bo")
    (hfr : FrameOutside s post (R ++ [freeGap s]) (heapFree s))
    (hR0 : ∀ i ∈ R, i.2 = 0 → i.1 % 8 = 0)
    (hRb : ∀ i ∈ R, Disj (globN s "bo", 88) i)
    (hRl : ∀ k ∈ ([40, 72] : List Nat), ∀ i ∈ R,
      Disj (memW s (globN s "bo" + k), 24) i) : TxBacking post := by
  obtain ⟨S, hWT⟩ := hW.1.2
  have hE := hW.2
  have hbw := bo_words hWT.2.2.1 hE.bo_nz
  have hlf : ∀ k ∈ ([40, 72] : List Nat),
      (memW s (globN s "bo" + k), 24) ∈ fixedObjects s := by
    intro k hk
    unfold fixedObjects
    apply List.mem_append_left
    apply List.mem_append_right
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · simp [blockOutObjects, hE.bo_nz, hE.bo40]
    · simp [blockOutObjects, hE.bo_nz, hE.bo72]
  have hlt : ∀ k ∈ ([40, 72] : List Nat),
      Allocated s (memW s (globN s "bo" + k), 24) ∧
      WordsOK s (memW s (globN s "bo" + k), 24) := by
    intro k hk
    exact (hWT.2.2.1.1 _ (hlf k hk)).resolve_left (by simp)
  have hu : ∀ i : Ivl, Allocated s i → WordsOK s i →
      (∀ j ∈ R, Disj i j) → IvlUnhit s post i := by
    intro i ha hw hd
    exact (allocated_ivl_survives_step (old := []) (new := [])
      hW.1.1.2 hAp hgrow (by simp) hR0 (by intro o ho; cases ho)
      (by simpa using hfr) hw.1 hw.2.1 ha (by simp) hd).2.2
  exact txBacking_of_unhit_headers hb hbo hbw.2.1
    (ivl_allocated_bound hW.1.1.2 hbw.1).2 (hu _ hbw.1 hbw.2 hRb)
    (fun k hk => (hlt k hk).2.1)
    (fun k hk => (ivl_allocated_bound hW.1.1.2 (hlt k hk).1).2)
    (fun k hk => hu _ (hlt k hk).1 (hlt k hk).2 (hRl k hk))

/-- Scratch-buffer separation from the record and both nested headers follows
from world typing; only the concrete callee frame remains to be supplied. -/
theorem txBacking_of_scratch_frame {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    {gs : List (String × Nat × Nat)} (hgs : ScratchSpec gs)
    (hW : TxWorld s) (hb : TxBacking s) (hAp : ArenaOK post)
    (hgrow : AllocatorGrows s post)
    (hbo : globN post "bo" = globN s "bo")
    (hfr : FrameOutside s post
      (gs.map (fun e => bufferRegion s (e.1, e.2.2)) ++ [freeGap s]) (heapFree s)) :
    TxBacking post := by
  obtain ⟨S, hWT⟩ := hW.1.2
  obtain ⟨Nd, htyped⟩ := (worldTyped_iff_with s S).mp hWT
  have hdisj : ∀ j ∈ worldTypedIvls s S Nd,
      ∀ i ∈ gs.map (fun e => bufferRegion s (e.1, e.2.2)), Disj j i := by
    intro j hj i hi
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hi
    exact disj_symm (bufferRegion_disj_le htyped (e.1, e.2.1)
      (hgs e he).1 (hgs e he).2.1 e.2.2 (hgs e he).2.2.2 j hj)
  apply txBacking_of_allocated_frame hW hb hAp hgrow hbo hfr
  · intro i hi
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hi
    exact bufferRegion_zero_aligned s e.1 e.2.2
      (by have := (hgs e he).2.2.1; omega)
  · exact hdisj _ (bo_mem_typed hW.2.bo_nz)
  · intro k hk
    apply hdisj
    unfold worldTypedIvls
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_right
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · simp [blockOutObjects, hW.2.bo_nz, hW.2.bo40]
    · simp [blockOutObjects, hW.2.bo_nz, hW.2.bo72]

end PtxP34

namespace PtxP34
open PtxP1

theorem create_ether_backing_resume_of_frame {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "create_ether") vs =
      some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) (hp : TxAfterCallBackingStrong s)
    (hfr : FrameOutside s post
      (etherScratchSpec.map (fun e => bufferRegion s (e.1, e.2.2)) ++ [freeGap s])
      (heapFree s)) : TxAfterCallBackingStrong {post with locals := s.locals} := by
  have hw := funSpec_at_lookup EvmEkFk.wkSc_create_ether s hc vs body callee ret hl
    (worldOK_callEntry hp.1.1.1 callee) (by rw [hr]; simp)
  rw [hr] at hw
  have hs := hw (Or.inl ⟨v, rfl⟩)
  refine ⟨create_ether_txAfterCallStrong_resume s vs body callee ret v post hc hl hr hp.1, ?_⟩
  exact txBacking_of_scratch_frame etherScratchSpec_ok hp.1.1 hp.2 hs.1.1.2
    ⟨hs.1.2.1, hs.2⟩
    (R16Shards.globN_eq_of_lookup (hs.1.2.2.1 _ (by decide))) hfr

theorem create_ether_backing_resume_of_header_words {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "create_ether") vs =
      some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) (hp : TxAfterCallBackingStrong s)
    (hdata : ∀ k ∈ ([40, 72] : List Nat),
      memW post (memW s (globN s "bo" + k)) = memW s (memW s (globN s "bo" + k))) :
    TxAfterCallBackingStrong {post with locals := s.locals} := by
  have hw := funSpec_at_lookup EvmEkFk.wkSc_create_ether s hc vs body callee ret hl
    (worldOK_callEntry hp.1.1.1 callee) (by rw [hr]; simp)
  rw [hr] at hw
  have hs := hw (Or.inl ⟨v, rfl⟩)
  have hbo : globN post "bo" = globN s "bo" :=
    R16Shards.globN_eq_of_lookup (hs.1.2.2.1 _ (by decide))
  refine ⟨create_ether_txAfterCallStrong_resume s vs body callee ret v post hc hl hr hp.1, ?_⟩
  apply txBacking_of_header_words hp.2 hbo ?_ hdata
  intro k hk
  have hW := hp.1.1
  obtain ⟨S, Nd, hWT, _, _⟩ := hp.1.2.2.2.2
  have hWTc := (R13Shards.worldTypedWith_with_locals s callee (s.clock - 1) S Nd).mpr hWT
  have hR : ∀ i ∈ R16WkAcctWs.bufRegions EvmEkFk.acctMutBufs
      (callEntryStateHOLFinite s callee), Disj i (globN s "bo", 88) := by
    intro i hi
    change i ∈ etherScratchSpec.map (fun e => bufferRegion s (e.1, e.2.2)) at hi
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hi
    exact bufferRegion_disj_le hWT (e.1, e.2.1) (etherScratchSpec_ok e he).1
      (etherScratchSpec_ok e he).2.1 e.2.2 (etherScratchSpec_ok e he).2.2.2 _
      (bo_mem_typed hW.2.bo_nz)
  apply hs.1.2.2.2.1 ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])
    (by decide) hW.2.bo_nz k
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl <;> simp
  · intro i hi hh
    change CellHits (globN s "bo" + k) i at hh
    have hd := hR i hi
    have hkbound : k + 8 ≤ 88 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl <;> omega
    rcases hd with hz | hz | hd | hd
    · change i.2 = 0 at hz
      have hz8 : i.1 % 8 = 0 := by
        change i ∈ etherScratchSpec.map (fun e => bufferRegion s (e.1, e.2.2)) at hi
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hi
        exact bufferRegion_zero_aligned s e.1 e.2.2
          (by have := (etherScratchSpec_ok e he).2.2.1; omega) hz
      have hb8 := (bo_words hWT.2.2.1 hW.2.bo_nz).2.1
      change globN s "bo" % 8 = 0 at hb8
      have hk8 : k % 8 = 0 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl <;> decide
      dsimp [CellHits] at hh
      omega
    · norm_num at hz
    · dsimp [CellHits] at hh
      dsimp at hd
      omega
    · dsimp [CellHits] at hh
      dsimp at hd
      omega

theorem encode_receipt_backing_of_frame (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4ReceiptReady s) (hb : TxBacking s)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "encode_receipt") vs =
      some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post))
    (hg : locN (callEntryStateHOLFinite s callee) "logs" = locN s "logs")
    (hfr : FrameOutside s post
      (receiptScratchSpec.map (fun e => bufferRegion s (e.1, e.2.2)) ++ [freeGap s])
      (heapFree s)) : TxBacking post := by
  have hL : LogsListOK (callEntryStateHOLFinite s callee)
      (locN (callEntryStateHOLFinite s callee) "logs") := by
    rw [hg]
    exact (R13Shards.logsListOK_with_locals s callee (s.clock - 1) _).mpr hp.2.1
  have hD : LogsDisjFixed (callEntryStateHOLFinite s callee)
      (locN (callEntryStateHOLFinite s callee) "logs") := by
    rw [hg]; exact hp.2.2.1
  have hw := funSpec_at_lookup h.wk_encode_receipt s hc vs body callee ret hl
    ⟨worldOK_callEntry hp.1.1.1 callee, hL, hD⟩ (by rw [hr]; simp)
  rw [hr] at hw
  have hs := hw (Or.inl ⟨v, rfl⟩)
  have hsc : globN post "scratch_ptr" = globN s "scratch_ptr" :=
    R16Shards.globN_eq_of_lookup (hs.2.2.1 _ (by decide))
  exact txBacking_of_scratch_frame receiptScratchSpec_ok hp.1.1 hb hs.1.2
    ⟨hs.2.1, by omega⟩
    (R16Shards.globN_eq_of_lookup (hs.2.2.1 _ (by decide))) hfr

theorem receipt_heapByteEff_frame {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (he : WkBlockTxEnc.HeapByteEff s post
      (receiptScratchSpec.map (fun e => bufferRegion s (e.1, e.2.2))) ["heap_ptr"]) :
    FrameOutside s post
      (receiptScratchSpec.map (fun e => bufferRegion s (e.1, e.2.2)) ++ [freeGap s])
      (heapFree s) := by
  intro a hk hf
  by_contra hn
  rcases he.cell_frame a hn with ⟨i, hi, hhit⟩ | hgap | hheap
  · exact hk i (List.mem_append_left _ hi) hhit.2
  · exact hk _ (List.mem_append_right _ (by simp)) hgap.2
  · exact hf hheap.2

theorem encode_receipt_backing_of_heapByteEff (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4ReceiptReady s) (hb : TxBacking s)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "encode_receipt") vs =
      some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post))
    (hg : locN (callEntryStateHOLFinite s callee) "logs" = locN s "logs")
    (he : WkBlockTxEnc.HeapByteEff (callEntryStateHOLFinite s callee) post
      (receiptScratchSpec.map (fun e => bufferRegion s (e.1, e.2.2))) ["heap_ptr"]) :
    TxBacking post := by
  apply encode_receipt_backing_of_frame h s vs body callee ret v post hc hp hb hl hr hg
  have hf := receipt_heapByteEff_frame (s := callEntryStateHOLFinite s callee) he
  exact hf

theorem ro_logs_encoded_bound : ReadOnlyFn (ofString "logs_encoded_bound") :=
  R16WkAcctWs.readOnlyFn_of_roProgR16 834 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_logs_encoded_bound rfl (fun _ => false)
    (fun _ hf => by cases hf) (by decide)

end PtxP34

namespace PtxP34
open WkBlockTxEnc InitECandidate.Solver.GuestTrapAndLookup

/-- Effects on buffers freshly allocated since `s` fold into the original heap frame. -/
theorem heapByteEff_trans_fresh {F : Type}
    {s mid post : PanSemStateFiniteExact 64 F} {R fresh : List Ivl} {gw : List String}
    (hpre : HeapByteEff s mid R gw)
    (hstep : HeapByteEff mid post (R ++ fresh) gw)
    (hfresh : ∀ i ∈ fresh, globN s "heap_ptr" ≤ i.1 ∧ i.1 + i.2 ≤ heapLimit) :
    HeapByteEff s post R gw := by
  have hp : HeapByteEff s mid (R ++ fresh) gw := hpre.mono
    (fun i hi _ => Or.inl ⟨i, List.mem_append_left _ hi, le_rfl, le_rfl⟩)
    (fun _ h => h)
  apply (hp.trans hstep).mono
  · intro i hi _
    rcases List.mem_append.mp hi with hi | hi
    · exact Or.inl ⟨i, hi, le_rfl, le_rfl⟩
    · exact Or.inr (Or.inr (hfresh i hi))
  · exact fun _ h => h

theorem heapByteEff_storeByte_fresh {F : Type}
    {s mid post : PanSemStateFiniteExact 64 F} {R : List Ivl} {gw : List String}
    (hpre : HeapByteEff s mid R gw) (addr value : ExpHOL 64)
    (hr : evaluateHOLFiniteState mid (.storeByte addr value) = (none, post))
    (haddr : ∀ a : BitVec 64,
      @evalHOLExact 64 F _ mid.toExact (fun a => Classical.propDecidable (mid.memaddrs a)) addr =
        some (.val (.word a)) →
      globN s "heap_ptr" ≤ a.toNat ∧ a.toNat + 1 ≤ heapLimit) :
    HeapByteEff s post R gw := by
  obtain ⟨he, _⟩ := M11.ByteRegionEffect.of_storeByte hr
    (Rl := [heapFree s]) (fun a ha _ => by
      have hb := haddr a ha
      exact ⟨heapFree s, by simp, hb.1, by dsimp [heapFree]; omega⟩)
  have hs : HeapByteEff mid post (R ++ [heapFree s]) gw :=
    (HeapByteEff.of_m11_bre hpre.arena he).mono
      (fun i hi _ => Or.inl ⟨i, List.mem_append_right _ hi, le_rfl, le_rfl⟩)
      (fun _ h => h)
  apply heapByteEff_trans_fresh hpre hs
  intro i hi
  simp only [List.mem_singleton] at hi
  subst i
  have hh := hpre.arena.2.2.1
  have hbase := le_trans hpre.hp_le hh
  dsimp [heapFree]
  omega

theorem rlp_encode_word_heapByteEff {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (dst w : BitVec 64) (v : ValueHOL 64)
    (R : List Ivl) (gw : List String) (hA : ArenaReady s)
    (hd : s.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (hw : s.locals.lookup (ofString "w") = some (.val (.word w)))
    (hR : ∃ i ∈ R, i.1 ≤ dst.toNat ∧ dst.toNat + 9 ≤ i.1 + i.2)
    (hr : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_encode_word) =
      (some (.returned v), post)) : HeapByteEff s post R gw := by
  have ht := eval_rlp_encode_word_body_exact s dst w R hA.1.code hA.1.memaddrs hd hw hR
    (by rw [hr]; simp)
  rw [hr] at ht
  obtain ⟨len, _, _, _, _, he⟩ := ht.1 v rfl
  exact HeapByteEff.of_m11_bre hA he

theorem rlp_encode_bytes_heapByteEff {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (dst src n : BitVec 64) (v : ValueHOL 64)
    (R : List Ivl) (gw : List String) (hA : ArenaReady s)
    (hd : s.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (hs : s.locals.lookup (ofString "src") = some (.val (.word src)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (hR : ∃ i ∈ R, i.1 ≤ dst.toNat ∧
      dst.toNat + rlpHeaderLenPure n.toNat + n.toNat ≤ i.1 + i.2)
    (hr : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes) =
      (some (.returned v), post)) : HeapByteEff s post R gw := by
  have ht := eval_rlp_encode_bytes_body_exact s dst src n R hA.1.code hA.1.memaddrs hd hs hn hR
    (by rw [hr]; simp)
  rw [hr] at ht
  obtain ⟨len, _, _, _, he⟩ := ht.1 v rfl
  exact HeapByteEff.of_m11_bre hA he

end PtxP34

namespace PtxP34
open WkBlockTxEnc

/-- Zeroing the fresh bloom buffer preserves the original receipt frame. -/
theorem heapByteEff_memzero_fresh {F : Type}
    {s mid post : PanSemStateFiniteExact 64 F} {R : List Ivl} {gw : List String}
    (hpre : HeapByteEff s mid R gw) (dstExp nExp : ExpHOL 64) (dst n : BitVec 64)
    (hd : @evalHOLExact 64 F _ mid.toExact
      (fun a => Classical.propDecidable (mid.memaddrs a)) dstExp = some (.val (.word dst)))
    (hn : @evalHOLExact 64 F _ mid.toExact
      (fun a => Classical.propDecidable (mid.memaddrs a)) nExp = some (.val (.word n)))
    (hfresh : globN s "heap_ptr" ≤ dst.toNat ∧ dst.toNat + n.toNat ≤ heapLimit)
    (hr : evaluateHOLFiniteState mid
      (.call (some (none, none)) (ofString "memzero") [dstExp, nExp]) = (none, post)) :
    HeapByteEff s post R gw := by
  have hz := eval_call_memzero_heap mid dstExp nExp dst n
    (R ++ [(dst.toNat, n.toNat)]) gw hpre.arena.1.code hpre.arena hd hn
    (fun _ => ⟨(dst.toNat, n.toNat), List.mem_append_right _ (by simp), le_rfl, le_rfl⟩)
    (by rw [hr]; simp)
  rw [hr] at hz
  apply heapByteEff_trans_fresh hpre (hz.1 rfl).2.1
  intro i hi
  simp only [List.mem_singleton] at hi
  subst i
  exact hfresh

end PtxP34

namespace PtxP34
open WkBlockTxEnc
open private WkBlockTxEnc.eval_call_logs_bloom WkBlockTxEnc.eval_call_local_encode_logs
  WkBlockTxEnc.logsEncodedSum from InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.EncodeReceipt

theorem heapByteEff_logs_bloom_fresh {F : Type}
    {s mid post : PanSemStateFiniteExact 64 F} {R : List Ivl}
    (hpre : HeapByteEff s mid R ["heap_ptr"])
    (logsExp outExp : ExpHOL 64) (logs out : BitVec 64)
    (hl : @evalHOLExact 64 F _ mid.toExact
      (fun a => Classical.propDecidable (mid.memaddrs a)) logsExp = some (.val (.word logs)))
    (ho : @evalHOLExact 64 F _ mid.toExact
      (fun a => Classical.propDecidable (mid.memaddrs a)) outExp = some (.val (.word out)))
    (hfresh : globN s "heap_ptr" ≤ out.toNat ∧ out.toNat + 256 ≤ heapLimit)
    (hpad : globN mid "keccak_pad" ≠ 0 →
      ∃ i ∈ R, i.1 ≤ globN mid "keccak_pad" ∧ globN mid "keccak_pad" + 136 ≤ i.1 + i.2)
    (hst : globN mid "keccak_st" ≠ 0 →
      ∃ i ∈ R, i.1 ≤ globN mid "keccak_st" ∧ globN mid "keccak_st" + 200 ≤ i.1 + i.2)
    (hr : evaluateHOLFiniteState mid
      (.call (some (none, none)) (ofString "logs_bloom") [logsExp, outExp]) = (none, post)) :
    HeapByteEff s post R ["heap_ptr"] := by
  have hb := WkBlockTxEnc.eval_call_logs_bloom mid logsExp outExp logs out (R ++ [(out.toNat, 256)])
    hpre.arena.1.code hpre.arena hl ho
    ⟨(out.toNat, 256), List.mem_append_right _ (by simp), le_rfl, le_rfl⟩
    (fun hn => by
      obtain ⟨i, hi, hb⟩ := hpad hn
      exact ⟨i, List.mem_append_left _ hi, hb⟩)
    (fun hn => by
      obtain ⟨i, hi, hb⟩ := hst hn
      exact ⟨i, List.mem_append_left _ hi, hb⟩)
    (by rw [hr]; simp) (by rw [hr]; simp)
  rw [hr] at hb
  apply heapByteEff_trans_fresh hpre hb.1
  intro i hi
  simp only [List.mem_singleton] at hi
  subst i
  exact hfresh

theorem heapByteEff_encode_logs_fresh {F : Type}
    {s mid post : PanSemStateFiniteExact 64 F} {R : List Ivl}
    (hpre : HeapByteEff s mid R ["heap_ptr"])
    (lname : String) (dstExp logsExp : ExpHOL 64) (dst logs : BitVec 64) (bound : Nat)
    (hA : ArenaOK s) (hma : s.memaddrs = ordinaryDomain)
    (hlogframe : HeapByteEff s mid [(dst.toNat, bound)] ["heap_ptr"])
    (hfresh : globN s "heap_ptr" ≤ dst.toNat ∧ dst.toNat + bound ≤ heapLimit)
    (hnz : logs.toNat ≠ 0) (hlogs : LogsListOK s logs.toNat)
    (harr : Allocated s (memW s logs.toNat, 8 * memW s (logs.toNat + 8)))
    (hfit : 9 + WkBlockTxEnc.logsEncodedSum s (memW s logs.toNat) (memW s (logs.toNat + 8)) ≤ bound)
    (hold : ∃ w : BitVec 64, mid.locals.lookup (ofString lname) = some (.val (.word w)))
    (hd : @evalHOLExact 64 F _ mid.toExact
      (fun a => Classical.propDecidable (mid.memaddrs a)) dstExp = some (.val (.word dst)))
    (hl : @evalHOLExact 64 F _ mid.toExact
      (fun a => Classical.propDecidable (mid.memaddrs a)) logsExp = some (.val (.word logs)))
    (hr : evaluateHOLFiniteState mid
      (.call (some (some (.local, ofString lname), none)) (ofString "encode_logs")
        [dstExp, logsExp]) = (none, post)) :
    HeapByteEff s post R ["heap_ptr"] := by
  have he := WkBlockTxEnc.eval_call_local_encode_logs s mid lname dstExp logsExp dst logs bound
    (R ++ [(dst.toNat, bound)]) ["heap_ptr"] hA hma hlogframe hfresh.1 hfresh.2
    (by decide) hnz hlogs harr hfit
    ⟨(dst.toNat, bound), List.mem_append_right _ (by simp), le_rfl, le_rfl⟩ hold hd hl
    (by rw [hr]; simp)
  rw [hr] at he
  obtain ⟨w, hw, hg, hl, heff⟩ := he.1 rfl
  apply heapByteEff_trans_fresh hpre heff
  intro i hi
  simp only [List.mem_singleton] at hi
  subst i
  exact hfresh

end PtxP34

namespace PtxP34
open WkBlockTxEnc

theorem heapByteEff_rlp_finish_list_fresh {F : Type}
    {s mid post : PanSemStateFiniteExact 64 F} {R : List Ivl} {gw : List String}
    (hpre : HeapByteEff s mid R gw)
    (lname : String) (dstExp endExp : ExpHOL 64) (dst pend : BitVec 64)
    (hold : ∃ w : BitVec 64, mid.locals.lookup (ofString lname) = some (.val (.word w)))
    (hd : @evalHOLExact 64 F _ mid.toExact
      (fun a => Classical.propDecidable (mid.memaddrs a)) dstExp = some (.val (.word dst)))
    (he : @evalHOLExact 64 F _ mid.toExact
      (fun a => Classical.propDecidable (mid.memaddrs a)) endExp = some (.val (.word pend)))
    (hle : dst.toNat + 9 ≤ pend.toNat)
    (hfresh : globN s "heap_ptr" ≤ dst.toNat ∧ pend.toNat ≤ heapLimit)
    (hr : evaluateHOLFiniteState mid
      (.call (some (some (.local, ofString lname), none)) (ofString "rlp_finish_list")
        [dstExp, endExp]) = (none, post)) : HeapByteEff s post R gw := by
  have ht := eval_call_local_rlp_finish_list mid lname dstExp endExp dst pend
    (R ++ [(dst.toNat, pend.toNat - dst.toNat)]) gw hpre.arena.1.code hpre.arena hold hd he
    hle (le_trans hfresh.2 (by decide))
    ⟨(dst.toNat, pend.toNat - dst.toNat), List.mem_append_right _ (by simp), le_rfl, by omega⟩
    (by rw [hr]; simp)
  rw [hr] at ht
  obtain ⟨w, hw, hb, hg, hl, heff⟩ := ht.1 rfl
  apply heapByteEff_trans_fresh hpre heff
  intro i hi
  simp only [List.mem_singleton] at hi
  subst i
  exact ⟨hfresh.1, by dsimp; omega⟩

end PtxP34

namespace PtxP34
open WkBlockTxEnc PtxP1

theorem txBacking_of_scratch_heapByteEff {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {gs : List (String × Nat × Nat)}
    (hgs : ScratchSpec gs) (hW : TxWorld s) (hb : TxBacking s)
    (he : HeapByteEff s post (gs.map (fun e => bufferRegion s (e.1, e.2.2))) ["heap_ptr"]) :
    TxBacking post := by
  apply txBacking_of_scratch_frame hgs hW hb he.arena.2
    ⟨he.hp_le, he.sp_le⟩
    (R16Shards.globN_eq_of_lookup (he.globals _ (by decide)))
  intro a hk hf
  by_contra hn
  rcases he.cell_frame a hn with ⟨i, hi, hhit⟩ | hgap | hheap
  · exact hk i (List.mem_append_left _ hi) hhit.2
  · exact hk _ (List.mem_append_right _ (by simp)) hgap.2
  · exact hf hheap.2

theorem receipt_backing_of_body_effect {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hp : Phase4ReceiptReady s) (hb : TxBacking s)
    (he : HeapByteEff s post
      (receiptScratchSpec.map (fun e => bufferRegion s (e.1, e.2.2))) ["heap_ptr"]) :
    TxBacking post :=
  txBacking_of_scratch_heapByteEff receiptScratchSpec_ok hp.1.1 hb he

end PtxP34

namespace PtxP34
open WkBlockTxEnc

/-- Snapshot current log memory with the entry allocation frontier. -/
theorem heapByteEff_snapshot {F : Type}
    {s mid : PanSemStateFiniteExact 64 F} {R fresh : List Ivl}
    (hA : ArenaOK s) (he : HeapByteEff s mid R ["heap_ptr"]) :
    HeapByteEff s {mid with globals := s.globals} R ["heap_ptr"] ∧
    HeapByteEff {mid with globals := s.globals} mid fresh ["heap_ptr"] := by
  have hAs : ArenaOK {mid with globals := s.globals} := arenaOK_congr rfl hA
  have hAR : ArenaReady {mid with globals := s.globals} :=
    ⟨guestInv_congr (s := mid) rfl rfl rfl rfl he.arena.1, hAs⟩
  constructor
  · exact ⟨hAR, he.memaddrs, le_rfl, rfl, le_rfl, he.be,
      fun _ _ => rfl, he.out_dom, he.cell_frame, he.byte_frame⟩
  · exact ⟨he.arena, rfl, he.hp_le, he.fp_eq, he.sp_le, rfl, he.globals,
      fun _ hn => False.elim (hn rfl), fun _ hn => False.elim (hn rfl),
      fun _ _ hn => False.elim (hn rfl)⟩

open private WkBlockTxEnc.logsEncodedSum from InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.EncodeReceipt

theorem heapByteEff_encode_logs_snapshot {F : Type}
    {s mid post : PanSemStateFiniteExact 64 F} {R : List Ivl}
    (hA : ArenaOK s) (hpre : HeapByteEff s mid R ["heap_ptr"])
    (lname : String) (dstExp logsExp : ExpHOL 64) (dst logs : BitVec 64) (bound : Nat)
    (hfresh : globN s "heap_ptr" ≤ dst.toNat ∧ dst.toNat + bound ≤ heapLimit)
    (hnz : logs.toNat ≠ 0)
    (hlogs : LogsListOK {mid with globals := s.globals} logs.toNat)
    (harr : Allocated {mid with globals := s.globals}
      (memW mid logs.toNat, 8 * memW mid (logs.toNat + 8)))
    (hfit : 9 + WkBlockTxEnc.logsEncodedSum mid (memW mid logs.toNat)
      (memW mid (logs.toNat + 8)) ≤ bound)
    (hold : ∃ w : BitVec 64, mid.locals.lookup (ofString lname) = some (.val (.word w)))
    (hd : @evalHOLExact 64 F _ mid.toExact
      (fun a => Classical.propDecidable (mid.memaddrs a)) dstExp = some (.val (.word dst)))
    (hl : @evalHOLExact 64 F _ mid.toExact
      (fun a => Classical.propDecidable (mid.memaddrs a)) logsExp = some (.val (.word logs)))
    (hr : evaluateHOLFiniteState mid
      (.call (some (some (.local, ofString lname), none)) (ofString "encode_logs")
        [dstExp, logsExp]) = (none, post)) : HeapByteEff s post R ["heap_ptr"] := by
  obtain ⟨hsnap, hf⟩ := heapByteEff_snapshot (fresh := [(dst.toNat, bound)]) hA hpre
  have hsnapmid : HeapByteEff {mid with globals := s.globals} mid R ["heap_ptr"] :=
    (heapByteEff_snapshot (fresh := R) hA hpre).2
  have hfit' : 9 + WkBlockTxEnc.logsEncodedSum {mid with globals := s.globals}
      (memW mid logs.toNat) (memW mid (logs.toNat + 8)) ≤ bound := by
    have heq : ∀ n, WkBlockTxEnc.logsEncodedSum {mid with globals := s.globals}
        (memW mid logs.toNat) n = WkBlockTxEnc.logsEncodedSum mid (memW mid logs.toNat) n := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => simp only [WkBlockTxEnc.logsEncodedSum, ih]; rfl
    rw [heq]
    exact hfit
  exact hsnap.trans (heapByteEff_encode_logs_fresh hsnapmid lname dstExp logsExp dst logs bound
    hsnap.arena.2 hsnap.arena.1.memaddrs hf hfresh hnz hlogs harr hfit' hold hd hl hr)

end PtxP34

namespace PtxP34
open WkBlockTxEnc
open private WkBlockTxEnc.receiptKeccakIvls WkBlockTxEnc.logsListOK_preserved
  WkBlockTxEnc.memW_eq_of_allocated_disj_fixed
  from InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.EncodeReceipt

theorem receipt_snapshot_logs {F : Type}
    {s mid : PanSemStateFiniteExact 64 F} {logs : Nat}
    (hA : ArenaOK s) (hma : s.memaddrs = ordinaryDomain)
    (he : HeapByteEff s mid (WkBlockTxEnc.receiptKeccakIvls s) ["heap_ptr"])
    (hnz : logs ≠ 0) (hL : LogsListOK s logs) (hD : LogsDisjFixed s logs) :
    LogsListOK {mid with globals := s.globals} logs ∧
    Allocated {mid with globals := s.globals} (memW mid logs, 8 * memW mid (logs + 8)) ∧
    memW mid logs = memW s logs ∧ memW mid (logs + 8) = memW s (logs + 8) := by
  have hs := (heapByteEff_snapshot (fresh := []) hA he).1
  have hLs := WkBlockTxEnc.logsListOK_preserved hA hma hs hnz hL hD
  rcases hL with hz | ⟨hw, ha, _⟩
  · exact False.elim (hnz hz)
  rcases hD with hz | ⟨harr, hdisj⟩
  · exact False.elim (hnz hz)
  have hd : ∀ f ∈ fixedObjects s, Disj (logs, 24) f :=
    fun f hf => hdisj _ (List.mem_append_left _ List.mem_cons_self) f hf
  have hm0 : memW mid logs = memW s logs :=
    WkBlockTxEnc.memW_eq_of_allocated_disj_fixed he hA hma ha hd hw.1
      (by simp) (by simp)
  have hm8 : memW mid (logs + 8) = memW s (logs + 8) :=
    WkBlockTxEnc.memW_eq_of_allocated_disj_fixed he hA hma ha hd
      (by have := hw.1; omega) (by simp) (by simp)
  refine ⟨hLs.2, ?_, hm0, hm8⟩
  rw [hm0, hm8]
  exact harr

end PtxP34

namespace PtxP34
open WkBlockTxEnc
open private WkBlockTxEnc.receiptKeccakIvls WkBlockTxEnc.logsEncodedSum
  WkBlockTxEnc.memW_eq_of_allocated_disj_fixed
  from InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.EncodeReceipt

theorem receipt_logs_sum_preserved {F : Type}
    {s mid : PanSemStateFiniteExact 64 F} {logs : Nat}
    (hA : ArenaOK s) (hma : s.memaddrs = ordinaryDomain)
    (he : HeapByteEff s mid (WkBlockTxEnc.receiptKeccakIvls s) ["heap_ptr"])
    (hnz : logs ≠ 0) (hL : LogsListOK s logs) (hD : LogsDisjFixed s logs) :
    WkBlockTxEnc.logsEncodedSum mid (memW mid logs) (memW mid (logs + 8)) =
      WkBlockTxEnc.logsEncodedSum s (memW s logs) (memW s (logs + 8)) := by
  obtain ⟨_, _, hm0, hm8⟩ := receipt_snapshot_logs hA hma he hnz hL hD
  rw [hm0, hm8]
  rcases hL with hz | ⟨_, _, _, _, hentries⟩
  · exact False.elim (hnz hz)
  rcases hD with hz | ⟨hal_arr, hdisj⟩
  · exact False.elim (hnz hz)
  have hdj_arr : ∀ f ∈ fixedObjects s,
      Disj (memW s logs, 8 * memW s (logs + 8)) f :=
    fun f hf => hdisj _ (List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self)) f hf
  have hsum : ∀ k, k ≤ memW s (logs + 8) →
      WkBlockTxEnc.logsEncodedSum mid (memW s logs) k =
        WkBlockTxEnc.logsEncodedSum s (memW s logs) k := by
    intro k hk
    induction k with
    | zero => rfl
    | succ k ih =>
      have hkl : k < memW s (logs + 8) := by omega
      obtain ⟨hwa, hle⟩ := hentries k hkl
      have ha64 : memW s logs + 8 * k < 2 ^ 64 := by
        have := M13.allocated_le_2pow64 hA hal_arr
        dsimp only at this
        omega
      have ha8 : (memW s logs + 8 * k) % 8 = 0 := by
        obtain ⟨_, hdom, _⟩ := hwa
        rw [hma, ordinaryDomain_iff] at hdom
        have hbv : (BitVec.ofNat 64 (memW s logs + 8 * k)).toNat = memW s logs + 8 * k :=
          Nat.mod_eq_of_lt ha64
        rw [hbv] at hdom
        exact hdom.1
      have hm_elem : memW mid (memW s logs + 8 * k) = memW s (memW s logs + 8 * k) :=
        WkBlockTxEnc.memW_eq_of_allocated_disj_fixed he hA hma hal_arr hdj_arr ha8
          (by dsimp; omega) (by dsimp; omega)
      let log := memW s (memW s logs + 8 * k)
      obtain ⟨hw_log, hin_log, _⟩ := hle
      have hal_log : Allocated s (log, 40) := Or.inl hin_log
      have howned : (log, 40) ∈ logOwnedIvls s log := by
        unfold logOwnedIvls
        refine List.mem_filter.2 ⟨by simp [logRecordIvls], ?_⟩
        simp only [bne_iff_ne, ne_eq, Prod.mk.injEq, not_and]
        intro _ h40
        omega
      have hflat : (log, 40) ∈ (List.range (memW s (logs + 8))).flatMap
          (fun i => logOwnedIvls s (memW s (memW s logs + 8 * i))) :=
        List.mem_flatMap.2 ⟨k, List.mem_range.2 hkl, howned⟩
      have hdj : ∀ f ∈ fixedObjects s, Disj (log, 40) f :=
        fun f hf => hdisj _ (List.mem_append_right _ hflat) f hf
      have hm16 : memW mid (log + 16) = memW s (log + 16) :=
        WkBlockTxEnc.memW_eq_of_allocated_disj_fixed he hA hma hal_log hdj
          (by have := hw_log.1; omega) (by dsimp [log]; omega) (by dsimp [log]; omega)
      have hm32 : memW mid (log + 32) = memW s (log + 32) :=
        WkBlockTxEnc.memW_eq_of_allocated_disj_fixed he hA hma hal_log hdj
          (by have := hw_log.1; omega) (by dsimp [log]; omega) (by dsimp [log]; omega)
      dsimp [log] at hm16 hm32
      simp only [WkBlockTxEnc.logsEncodedSum, ih (by omega), hm_elem, hm16, hm32]
  exact hsum _ le_rfl

end PtxP34

namespace PtxP34
open WkBlockTxEnc
open private WkBlockTxEnc.receiptKeccakIvls WkBlockTxEnc.logsEncodedSum
  from InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.EncodeReceipt

theorem receipt_encode_logs_frame {F : Type}
    {s mid post : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) (hma : s.memaddrs = ordinaryDomain)
    (hpre : HeapByteEff s mid (WkBlockTxEnc.receiptKeccakIvls s) ["heap_ptr"])
    (lname : String) (dstExp logsExp : ExpHOL 64) (dst logs : BitVec 64) (bound : Nat)
    (hfresh : globN s "heap_ptr" ≤ dst.toNat ∧ dst.toNat + bound ≤ heapLimit)
    (hnz : logs.toNat ≠ 0) (hL : LogsListOK s logs.toNat) (hD : LogsDisjFixed s logs.toNat)
    (hfit : 9 + WkBlockTxEnc.logsEncodedSum s (memW s logs.toNat)
      (memW s (logs.toNat + 8)) ≤ bound)
    (hold : ∃ w : BitVec 64, mid.locals.lookup (ofString lname) = some (.val (.word w)))
    (hd : @evalHOLExact 64 F _ mid.toExact
      (fun a => Classical.propDecidable (mid.memaddrs a)) dstExp = some (.val (.word dst)))
    (hl : @evalHOLExact 64 F _ mid.toExact
      (fun a => Classical.propDecidable (mid.memaddrs a)) logsExp = some (.val (.word logs)))
    (hr : evaluateHOLFiniteState mid
      (.call (some (some (.local, ofString lname), none)) (ofString "encode_logs")
        [dstExp, logsExp]) = (none, post)) :
    HeapByteEff s post (WkBlockTxEnc.receiptKeccakIvls s) ["heap_ptr"] := by
  obtain ⟨hLs, harr, _, _⟩ := receipt_snapshot_logs hA hma hpre hnz hL hD
  apply heapByteEff_encode_logs_snapshot hA hpre lname dstExp logsExp dst logs bound
    hfresh hnz hLs harr ?_ hold hd hl hr
  rw [receipt_logs_sum_preserved hA hma hpre hnz hL hD]
  exact hfit

end PtxP34

namespace PtxP34
open WkBlockTxEnc
open private WkBlockTxEnc.receiptKeccakIvls
  from InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.EncodeReceipt

theorem receipt_logs_bloom_frame {F : Type}
    {s mid post : PanSemStateFiniteExact 64 F}
    (hpre : HeapByteEff s mid (WkBlockTxEnc.receiptKeccakIvls s) ["heap_ptr"])
    (logsExp outExp : ExpHOL 64) (logs out : BitVec 64)
    (hl : @evalHOLExact 64 F _ mid.toExact
      (fun a => Classical.propDecidable (mid.memaddrs a)) logsExp = some (.val (.word logs)))
    (ho : @evalHOLExact 64 F _ mid.toExact
      (fun a => Classical.propDecidable (mid.memaddrs a)) outExp = some (.val (.word out)))
    (hfresh : globN s "heap_ptr" ≤ out.toNat ∧ out.toNat + 256 ≤ heapLimit)
    (hr : evaluateHOLFiniteState mid
      (.call (some (none, none)) (ofString "logs_bloom") [logsExp, outExp]) = (none, post)) :
    HeapByteEff s post (WkBlockTxEnc.receiptKeccakIvls s) ["heap_ptr"] := by
  have hp : globN mid "keccak_pad" = globN s "keccak_pad" :=
    R16Shards.globN_eq_of_lookup (hpre.globals _ (by decide))
  have hs : globN mid "keccak_st" = globN s "keccak_st" :=
    R16Shards.globN_eq_of_lookup (hpre.globals _ (by decide))
  apply heapByteEff_logs_bloom_fresh hpre logsExp outExp logs out hl ho hfresh ?_ ?_ hr
  · intro hn
    rw [hp] at hn ⊢
    refine ⟨(globN s "keccak_pad", 136), ?_, le_rfl, le_rfl⟩
    simp [WkBlockTxEnc.receiptKeccakIvls, hn]
  · intro hn
    rw [hs] at hn ⊢
    refine ⟨(globN s "keccak_st", 200), ?_, le_rfl, le_rfl⟩
    simp [WkBlockTxEnc.receiptKeccakIvls, hn]

end PtxP34

namespace PtxP34
open WkBlockTxEnc
open private WkBlockTxEnc.receiptKeccakIvls
  from InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.EncodeReceipt

/-- The bloom call and its RLP serialization in the receipt body share the
entry scratch frame; both output buffers are fresh relative to that entry. -/
theorem receipt_bloom_encode_frame {F : Type}
    {s mid post : PanSemStateFiniteExact 64 F}
    (hpre : HeapByteEff s mid (WkBlockTxEnc.receiptKeccakIvls s) ["heap_ptr"])
    (logs bloom dst old : BitVec 64)
    (hl : mid.locals.lookup (ofString "logs") = some (.val (.word logs)))
    (hb : mid.locals.lookup (ofString "bloom") = some (.val (.word bloom)))
    (hd : mid.locals.lookup (ofString "p") = some (.val (.word dst)))
    (hw : mid.locals.lookup (ofString "w") = some (.val (.word old)))
    (hbf : globN s "heap_ptr" ≤ bloom.toNat ∧ bloom.toNat + 256 ≤ heapLimit)
    (hdf : globN s "heap_ptr" ≤ dst.toNat ∧ dst.toNat + 265 ≤ heapLimit)
    (hr : evaluateHOLFiniteState mid
      (.seq
        (.call (some (none, none)) (ofString "logs_bloom")
          [.var .local (ofString "logs"), .var .local (ofString "bloom")])
        (.call (some (some (.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
          [.var .local (ofString "p"), .var .local (ofString "bloom"), .const 256])) =
      (none, post)) :
    HeapByteEff s post (WkBlockTxEnc.receiptKeccakIvls s) ["heap_ptr"] ∧
    ∃ w : BitVec 64, w.toNat ≤ 265 ∧
      post.locals = mid.locals.update (ofString "w", .val (.word w)) := by
  rw [evaluateHOLFiniteState_seq_line780] at hr
  rcases hc : evaluateHOLFiniteState mid
      (.call (some (none, none)) (ofString "logs_bloom")
        [.var .local (ofString "logs"), .var .local (ofString "bloom")]) with ⟨r, next⟩
  rw [hc] at hr
  cases r with
  | some r => simp at hr
  | none =>
    dsimp only at hr
    have hnext := receipt_logs_bloom_frame hpre
      (.var .local (ofString "logs")) (.var .local (ofString "bloom")) logs bloom hl hb hbf hc
    have hloc : next.locals = mid.locals := (ignored_call_fall_locals mid next
      (ofString "logs_bloom") _ hc).1
    have he := eval_call_local_rlp_encode_bytes next "w"
      (.var .local (ofString "p")) (.var .local (ofString "bloom")) (.const 256)
      dst bloom 256#64
      (WkBlockTxEnc.receiptKeccakIvls s ++ [(dst.toNat, 265)]) ["heap_ptr"]
      hnext.arena.1.code hnext.arena ⟨old, by rw [hloc]; exact hw⟩
      (by change next.locals.lookup _ = _; rw [hloc]; exact hd)
      (by change next.locals.lookup _ = _; rw [hloc]; exact hb) rfl
      ⟨(dst.toNat, 265), List.mem_append_right _ (by simp), le_rfl, by
        have hbnd := rlpHeaderLenPure_bounds 256
        change dst.toNat + rlpHeaderLenPure 256 + 256 ≤ dst.toNat + 265
        omega⟩ (by rw [hr]; simp)
    rw [hr] at he
    obtain ⟨w, hbound, _, _, hlocals, heff⟩ := he.1 rfl
    refine ⟨heapByteEff_trans_fresh hnext heff ?_, w, ?_, ?_⟩
    · intro i hi
      simp only [List.mem_singleton] at hi
      subst i
      exact hdf
    · have hbnd := rlpHeaderLenPure_bounds 256
      change w.toNat ≤ rlpHeaderLenPure 256 + 256 at hbound
      omega
    · rw [hloc] at hlocals
      exact hlocals

end PtxP34

namespace PtxP34
open WkBlockTxEnc
open private WkBlockTxEnc.receiptKeccakIvls WkBlockTxEnc.logsEncodedSum
  WkBlockTxEnc.eval_call_local_encode_logs
  from InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.EncodeReceipt

/-- Keep the encoded length and local update alongside the receipt frame, so
the enclosing body can advance `p` and discharge the final-list bounds. -/
theorem receipt_encode_logs_frame_result {F : Type}
    {s mid post : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) (hma : s.memaddrs = ordinaryDomain)
    (hpre : HeapByteEff s mid (WkBlockTxEnc.receiptKeccakIvls s) ["heap_ptr"])
    (lname : String) (dstExp logsExp : ExpHOL 64) (dst logs : BitVec 64) (bound : Nat)
    (hfresh : globN s "heap_ptr" ≤ dst.toNat ∧ dst.toNat + bound ≤ heapLimit)
    (hnz : logs.toNat ≠ 0) (hL : LogsListOK s logs.toNat) (hD : LogsDisjFixed s logs.toNat)
    (hfit : 9 + WkBlockTxEnc.logsEncodedSum s (memW s logs.toNat)
      (memW s (logs.toNat + 8)) ≤ bound)
    (hold : ∃ w : BitVec 64, mid.locals.lookup (ofString lname) = some (.val (.word w)))
    (hd : @evalHOLExact 64 F _ mid.toExact
      (fun a => Classical.propDecidable (mid.memaddrs a)) dstExp = some (.val (.word dst)))
    (hl : @evalHOLExact 64 F _ mid.toExact
      (fun a => Classical.propDecidable (mid.memaddrs a)) logsExp = some (.val (.word logs)))
    (hr : evaluateHOLFiniteState mid
      (.call (some (some (.local, ofString lname), none)) (ofString "encode_logs")
        [dstExp, logsExp]) = (none, post)) :
    HeapByteEff s post (WkBlockTxEnc.receiptKeccakIvls s) ["heap_ptr"] ∧
    ∃ w : BitVec 64, w.toNat ≤ bound ∧ post.globals = mid.globals ∧
      post.locals = mid.locals.update (ofString lname, .val (.word w)) := by
  have hframe := receipt_encode_logs_frame hA hma hpre lname dstExp logsExp dst logs bound
    hfresh hnz hL hD hfit hold hd hl hr
  obtain ⟨hLs, harr, _, _⟩ := receipt_snapshot_logs hA hma hpre hnz hL hD
  obtain ⟨hsnap, hf⟩ := heapByteEff_snapshot (fresh := [(dst.toNat, bound)]) hA hpre
  have hsum : WkBlockTxEnc.logsEncodedSum {mid with globals := s.globals}
      (memW mid logs.toNat) (memW mid (logs.toNat + 8)) =
      WkBlockTxEnc.logsEncodedSum s (memW s logs.toNat) (memW s (logs.toNat + 8)) := by
    have heq : ∀ n, WkBlockTxEnc.logsEncodedSum {mid with globals := s.globals}
        (memW mid logs.toNat) n = WkBlockTxEnc.logsEncodedSum mid (memW mid logs.toNat) n := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => simp only [WkBlockTxEnc.logsEncodedSum, ih]; rfl
    rw [heq, receipt_logs_sum_preserved hA hma hpre hnz hL hD]
  have he := WkBlockTxEnc.eval_call_local_encode_logs {mid with globals := s.globals} mid
    lname dstExp logsExp dst logs bound [(dst.toNat, bound)] ["heap_ptr"]
    hsnap.arena.2 hsnap.arena.1.memaddrs hf hfresh.1 hfresh.2 (by decide) hnz hLs harr
    (by change 9 + WkBlockTxEnc.logsEncodedSum {mid with globals := s.globals}
          (memW mid logs.toNat) (memW mid (logs.toNat + 8)) ≤ bound
        rw [hsum]; exact hfit)
    ⟨(dst.toNat, bound), by simp, le_rfl, le_rfl⟩ hold hd hl (by rw [hr]; simp)
  rw [hr] at he
  obtain ⟨w, hw, hg, hl, _⟩ := he.1 rfl
  refine ⟨hframe, w, ?_, hg, hl⟩
  change w.toNat ≤ 9 + WkBlockTxEnc.logsEncodedSum {mid with globals := s.globals}
    (memW mid logs.toNat) (memW mid (logs.toNat + 8)) at hw
  rw [hsum] at hw
  exact le_trans hw hfit

end PtxP34

namespace PtxP34
open WkBlockTxEnc
open private WkBlockTxEnc.receiptKeccakIvls
  from InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.EncodeReceipt

/-- Advance the receipt cursor by the encoded log length and finalize its RLP
list while preserving the entry scratch frame. -/
theorem receipt_advance_finish_frame {F : Type}
    {s mid post : PanSemStateFiniteExact 64 F}
    (hpre : HeapByteEff s mid (WkBlockTxEnc.receiptKeccakIvls s) ["heap_ptr"])
    (start p w : BitVec 64)
    (hs : mid.locals.lookup (ofString "start") = some (.val (.word start)))
    (hp : mid.locals.lookup (ofString "p") = some (.val (.word p)))
    (hw : mid.locals.lookup (ofString "w") = some (.val (.word w)))
    (hle : start.toNat + 9 ≤ p.toNat)
    (hfresh : globN s "heap_ptr" ≤ start.toNat ∧ p.toNat + w.toNat ≤ heapLimit)
    (hr : evaluateHOLFiniteState mid
      (.seq (.assign .local (ofString "p")
        (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
        (.call (some (some (.local, ofString "w"), none)) (ofString "rlp_finish_list")
          [.var .local (ofString "start"), .var .local (ofString "p")])) = (none, post)) :
    HeapByteEff s post (WkBlockTxEnc.receiptKeccakIvls s) ["heap_ptr"] := by
  have hn : (p + w).toNat = p.toNat + w.toNat := by
    rw [BitVec.toNat_add]
    exact Nat.mod_eq_of_lt (lt_of_le_of_lt hfresh.2 (by decide))
  have ha : evaluateHOLFiniteState mid
      (.assign .local (ofString "p")
        (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])) =
      (none, setVarHOLFinite (ofString "p") (.val (.word (p + w))) mid) := by
    rw [evaluateHOLFiniteState_assign]
    have hev : @evalHOLExact 64 F _ mid.toExact
        (fun a => Classical.propDecidable (mid.memaddrs a))
        (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]) =
        some (.val (.word (p + w))) := by
      simp [evalHOLExact, evalListHOLExact, hp, hw, wordOpHOL, wordOp, valueIsWord, valueWord]
    have hv : mid.isValidValueHOLFinite .local (ofString "p") (.val (.word (p + w))) = true := by
      simp [PanSemStateFiniteExact.isValidValueHOLFinite, lookupKvarHOLExact, hp,
        shapeOfHOLExact, shapeEqHOL]
    rw [hev]
    dsimp only
    rw [if_pos hv]
    rfl
  rw [evaluateHOLFiniteState_seq_line780, ha] at hr
  dsimp only at hr
  let next := setVarHOLFinite (ofString "p") (.val (.word (p + w))) mid
  have he : HeapByteEff s next (WkBlockTxEnc.receiptKeccakIvls s) ["heap_ptr"] :=
    hpre.locals_clock next.locals next.clock
  apply heapByteEff_rlp_finish_list_fresh he "w"
    (.var .local (ofString "start")) (.var .local (ofString "p")) start (p + w)
  · exact ⟨w, by simp [next, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hw,
      show ofString "p" ≠ ofString "w" by decide]⟩
  · simpa [evalHOLExact, next, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "p" ≠ ofString "start" by decide] using hs
  · simp [evalHOLExact, next, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  · rw [hn]; omega
  · exact ⟨hfresh.1, hn ▸ hfresh.2⟩
  · exact hr

end PtxP34

namespace PtxP34
open WkBlockTxEnc
open private WkBlockTxEnc.receiptKeccakIvls WkBlockTxEnc.logsEncodedSum
  from InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.EncodeReceipt

/-- The concrete log-encoding suffix threads the entry frame through the
returned length, cursor advance, and final RLP list write. -/
theorem receipt_logs_finish_frame {F : Type}
    {s mid post : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) (hma : s.memaddrs = ordinaryDomain)
    (hpre : HeapByteEff s mid (WkBlockTxEnc.receiptKeccakIvls s) ["heap_ptr"])
    (start p logs old : BitVec 64) (bound : Nat)
    (hs : mid.locals.lookup (ofString "start") = some (.val (.word start)))
    (hp : mid.locals.lookup (ofString "p") = some (.val (.word p)))
    (hl : mid.locals.lookup (ofString "logs") = some (.val (.word logs)))
    (hw : mid.locals.lookup (ofString "w") = some (.val (.word old)))
    (hle : start.toNat + 9 ≤ p.toNat)
    (hfresh : globN s "heap_ptr" ≤ start.toNat ∧ p.toNat + bound ≤ heapLimit)
    (hnz : logs.toNat ≠ 0) (hL : LogsListOK s logs.toNat) (hD : LogsDisjFixed s logs.toNat)
    (hfit : 9 + WkBlockTxEnc.logsEncodedSum s (memW s logs.toNat)
      (memW s (logs.toNat + 8)) ≤ bound)
    (hr : evaluateHOLFiniteState mid
      (.seq
        (.call (some (some (.local, ofString "w"), none)) (ofString "encode_logs")
          [.var .local (ofString "p"), .var .local (ofString "logs")])
        (.seq (.assign .local (ofString "p")
          (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
          (.call (some (some (.local, ofString "w"), none)) (ofString "rlp_finish_list")
            [.var .local (ofString "start"), .var .local (ofString "p")]))) = (none, post)) :
    HeapByteEff s post (WkBlockTxEnc.receiptKeccakIvls s) ["heap_ptr"] := by
  rw [evaluateHOLFiniteState_seq_line780] at hr
  rcases hc : evaluateHOLFiniteState mid
      (.call (some (some (.local, ofString "w"), none)) (ofString "encode_logs")
        [.var .local (ofString "p"), .var .local (ofString "logs")]) with ⟨r, next⟩
  rw [hc] at hr
  cases r with
  | some r => simp at hr
  | none =>
    dsimp only at hr
    obtain ⟨he, w, hb, _, hloc⟩ := receipt_encode_logs_frame_result hA hma hpre "w"
      (.var .local (ofString "p")) (.var .local (ofString "logs")) p logs bound
      ⟨by omega, hfresh.2⟩ hnz hL hD hfit ⟨old, hw⟩ hp hl hc
    apply receipt_advance_finish_frame he start p w
    · rw [hloc]
      simpa [HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "w" ≠ ofString "start" by decide] using hs
    · rw [hloc]
      simpa [HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "w" ≠ ofString "p" by decide] using hp
    · rw [hloc]
      simp [HolFiniteMapExact.lookup_update, FUPDATE]
    · exact hle
    · exact ⟨hfresh.1, by omega⟩
    · exact hr

end PtxP34

namespace PtxP34
open WkBlockTxEnc
open private WkBlockTxEnc.receiptKeccakIvls WkBlockTxEnc.logsEncodedSum
  from InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.EncodeReceipt

/-- The receipt suffix after bloom serialization advances past that encoding,
encodes the logs, and finalizes the list within the fresh allocation. -/
theorem receipt_advance_logs_finish_frame {F : Type}
    {s mid post : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) (hma : s.memaddrs = ordinaryDomain)
    (hpre : HeapByteEff s mid (WkBlockTxEnc.receiptKeccakIvls s) ["heap_ptr"])
    (start p logs w : BitVec 64) (bound : Nat)
    (hs : mid.locals.lookup (ofString "start") = some (.val (.word start)))
    (hp : mid.locals.lookup (ofString "p") = some (.val (.word p)))
    (hl : mid.locals.lookup (ofString "logs") = some (.val (.word logs)))
    (hw : mid.locals.lookup (ofString "w") = some (.val (.word w)))
    (hle : start.toNat + 9 ≤ p.toNat)
    (hfresh : globN s "heap_ptr" ≤ start.toNat ∧ p.toNat + w.toNat + bound ≤ heapLimit)
    (hnz : logs.toNat ≠ 0) (hL : LogsListOK s logs.toNat) (hD : LogsDisjFixed s logs.toNat)
    (hfit : 9 + WkBlockTxEnc.logsEncodedSum s (memW s logs.toNat)
      (memW s (logs.toNat + 8)) ≤ bound)
    (hr : evaluateHOLFiniteState mid
      (.seq (.assign .local (ofString "p")
        (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
        (.seq
          (.call (some (some (.local, ofString "w"), none)) (ofString "encode_logs")
            [.var .local (ofString "p"), .var .local (ofString "logs")])
          (.seq (.assign .local (ofString "p")
            (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
            (.call (some (some (.local, ofString "w"), none)) (ofString "rlp_finish_list")
              [.var .local (ofString "start"), .var .local (ofString "p")])))) = (none, post)) :
    HeapByteEff s post (WkBlockTxEnc.receiptKeccakIvls s) ["heap_ptr"] := by
  have hn : (p + w).toNat = p.toNat + w.toNat := by
    rw [BitVec.toNat_add]
    apply Nat.mod_eq_of_lt
    have hlim : heapLimit < 2 ^ 64 := by decide
    omega
  have ha : evaluateHOLFiniteState mid
      (.assign .local (ofString "p")
        (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])) =
      (none, setVarHOLFinite (ofString "p") (.val (.word (p + w))) mid) := by
    rw [evaluateHOLFiniteState_assign]
    have hev : @evalHOLExact 64 F _ mid.toExact
        (fun a => Classical.propDecidable (mid.memaddrs a))
        (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]) =
        some (.val (.word (p + w))) := by
      simp [evalHOLExact, evalListHOLExact, hp, hw, wordOpHOL, wordOp, valueIsWord, valueWord]
    have hv : mid.isValidValueHOLFinite .local (ofString "p") (.val (.word (p + w))) = true := by
      simp [PanSemStateFiniteExact.isValidValueHOLFinite, lookupKvarHOLExact, hp,
        shapeOfHOLExact, shapeEqHOL]
    rw [hev]
    dsimp only
    rw [if_pos hv]
    rfl
  rw [evaluateHOLFiniteState_seq_line780, ha] at hr
  dsimp only at hr
  let next := setVarHOLFinite (ofString "p") (.val (.word (p + w))) mid
  have he : HeapByteEff s next (WkBlockTxEnc.receiptKeccakIvls s) ["heap_ptr"] :=
    hpre.locals_clock next.locals next.clock
  apply receipt_logs_finish_frame hA hma he start (p + w) logs w bound
  · simpa [next, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "p" ≠ ofString "start" by decide] using hs
  · simp [next, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  · simpa [next, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "p" ≠ ofString "logs" by decide] using hl
  · simpa [next, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "p" ≠ ofString "w" by decide] using hw
  · rw [hn]; omega
  · exact ⟨hfresh.1, by rw [hn]; exact hfresh.2⟩
  · exact hnz
  · exact hL
  · exact hD
  · exact hfit
  · exact hr

end PtxP34

namespace PtxP34
open WkBlockTxEnc
open private WkBlockTxEnc.receiptKeccakIvls WkBlockTxEnc.logsEncodedSum
  from InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.EncodeReceipt

/-- Compose the concrete receipt body from bloom generation through final
list encoding, using only the entry log invariants and fresh-buffer bounds. -/
theorem receipt_bloom_logs_finish_frame {F : Type}
    {s mid post : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) (hma : s.memaddrs = ordinaryDomain)
    (hpre : HeapByteEff s mid (WkBlockTxEnc.receiptKeccakIvls s) ["heap_ptr"])
    (start p logs bloom old : BitVec 64) (bound : Nat)
    (hs : mid.locals.lookup (ofString "start") = some (.val (.word start)))
    (hp : mid.locals.lookup (ofString "p") = some (.val (.word p)))
    (hl : mid.locals.lookup (ofString "logs") = some (.val (.word logs)))
    (hb : mid.locals.lookup (ofString "bloom") = some (.val (.word bloom)))
    (hw : mid.locals.lookup (ofString "w") = some (.val (.word old)))
    (hle : start.toNat + 9 ≤ p.toNat)
    (hfresh : globN s "heap_ptr" ≤ start.toNat ∧ p.toNat + 265 + bound ≤ heapLimit)
    (hbf : globN s "heap_ptr" ≤ bloom.toNat ∧ bloom.toNat + 256 ≤ heapLimit)
    (hnz : logs.toNat ≠ 0) (hL : LogsListOK s logs.toNat) (hD : LogsDisjFixed s logs.toNat)
    (hfit : 9 + WkBlockTxEnc.logsEncodedSum s (memW s logs.toNat)
      (memW s (logs.toNat + 8)) ≤ bound)
    (hr : evaluateHOLFiniteState mid
      (.seq
        (.call (some (none, none)) (ofString "logs_bloom")
          [.var .local (ofString "logs"), .var .local (ofString "bloom")])
        (.seq
          (.call (some (some (.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
            [.var .local (ofString "p"), .var .local (ofString "bloom"), .const 256])
          (.seq (.assign .local (ofString "p")
            (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
            (.seq
              (.call (some (some (.local, ofString "w"), none)) (ofString "encode_logs")
                [.var .local (ofString "p"), .var .local (ofString "logs")])
              (.seq (.assign .local (ofString "p")
                (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                (.call (some (some (.local, ofString "w"), none)) (ofString "rlp_finish_list")
                  [.var .local (ofString "start"), .var .local (ofString "p")])))))) = (none, post)) :
    HeapByteEff s post (WkBlockTxEnc.receiptKeccakIvls s) ["heap_ptr"] := by
  rw [← evaluate_seq_assoc, evaluateHOLFiniteState_seq_line780] at hr
  rcases hc : evaluateHOLFiniteState mid
      (.seq
        (.call (some (none, none)) (ofString "logs_bloom")
          [.var .local (ofString "logs"), .var .local (ofString "bloom")])
        (.call (some (some (.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
          [.var .local (ofString "p"), .var .local (ofString "bloom"), .const 256])) with ⟨r, next⟩
  rw [hc] at hr
  cases r with
  | some r => simp at hr
  | none =>
    dsimp only at hr
    obtain ⟨he, w, hwb, hloc⟩ := receipt_bloom_encode_frame hpre logs bloom p old hl hb hp hw
      hbf ⟨by omega, by omega⟩ hc
    apply receipt_advance_logs_finish_frame hA hma he start p logs w bound
    · rw [hloc]
      simpa [HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "w" ≠ ofString "start" by decide] using hs
    · rw [hloc]
      simpa [HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "w" ≠ ofString "p" by decide] using hp
    · rw [hloc]
      simpa [HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "w" ≠ ofString "logs" by decide] using hl
    · rw [hloc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    · exact hle
    · exact ⟨hfresh.1, by omega⟩
    · exact hnz
    · exact hL
    · exact hD
    · exact hfit
    · exact hr

end PtxP34

namespace PtxP34
open WkBlockTxEnc

/-- Returning a value only clears locals, preserving the accumulated frame. -/
theorem heapByteEff_return {F : Type}
    {s mid post : PanSemStateFiniteExact 64 F} {R : List Ivl} {gw : List String}
    (he : HeapByteEff s mid R gw) (e : ExpHOL 64) (v : ValueHOL 64)
    (hr : evaluateHOLFiniteState mid (.return e) = (some (.returned v), post)) :
    HeapByteEff s post R gw := by
  rw [evaluateHOLFiniteState_return] at hr
  split at hr
  · cases hr
  · split at hr
    · have hp := (Prod.mk.inj hr).2
      subst post
      exact he.locals_clock _ _
    · cases hr

/-- A fresh transaction-type byte followed by the receipt return preserves
the same entry frame as the untyped receipt return. -/
theorem heapByteEff_storeByte_return_fresh {F : Type}
    {s mid post : PanSemStateFiniteExact 64 F} {R : List Ivl} {gw : List String}
    (he : HeapByteEff s mid R gw) (addr value result : ExpHOL 64) (v : ValueHOL 64)
    (ha : ∀ a : BitVec 64,
      @evalHOLExact 64 F _ mid.toExact (fun a => Classical.propDecidable (mid.memaddrs a)) addr =
        some (.val (.word a)) →
      globN s "heap_ptr" ≤ a.toNat ∧ a.toNat + 1 ≤ heapLimit)
    (hr : evaluateHOLFiniteState mid (.seq (.storeByte addr value) (.return result)) =
      (some (.returned v), post)) : HeapByteEff s post R gw := by
  rw [evaluateHOLFiniteState_seq_line780] at hr
  rcases hc : evaluateHOLFiniteState mid (.storeByte addr value) with ⟨r, next⟩
  rw [hc] at hr
  cases r with
  | none =>
    dsimp only at hr
    exact heapByteEff_return (heapByteEff_storeByte_fresh he addr value hc ha) result v hr
  | some r =>
    have hn : ∀ v, (evaluateHOLFiniteState mid (.storeByte addr value)).1 ≠ some (.returned v) := by
      intro v
      rw [evaluateHOLFiniteState_storeByte]
      split <;> try simp
      split <;> try simp
      split <;> simp
    have hv := congrArg Prod.fst hr
    exact False.elim (hn v (by simpa [hc] using hv))

end PtxP34

namespace PtxP34
open WkBlockTxEnc

/-- Frame the receipt's optional type-prefix write and its two return paths. -/
theorem heapByteEff_optional_prefix_return {F : Type}
    {s mid post : PanSemStateFiniteExact 64 F} {R : List Ivl} {gw : List String}
    (he : HeapByteEff s mid R gw) (cond addr value typed plain : ExpHOL 64) (v : ValueHOL 64)
    (ha : ∀ a : BitVec 64,
      @evalHOLExact 64 F _ mid.toExact (fun a => Classical.propDecidable (mid.memaddrs a)) addr =
        some (.val (.word a)) →
      globN s "heap_ptr" ≤ a.toNat ∧ a.toNat + 1 ≤ heapLimit)
    (hr : evaluateHOLFiniteState mid
      (.seq (.ite cond (.seq (.storeByte addr value) (.return typed)) .skip)
        (.return plain)) = (some (.returned v), post)) : HeapByteEff s post R gw := by
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hr
  split at hr
  · split at hr
    · exact heapByteEff_return he plain v (by simpa only [evaluateHOLFiniteState_skip] using hr)
    · rcases hc : evaluateHOLFiniteState mid (.seq (.storeByte addr value) (.return typed)) with ⟨r, next⟩
      rw [hc] at hr
      cases r with
      | some r =>
        have hp := (Prod.mk.inj hr).2
        have hv := (Option.some.inj (Prod.mk.inj hr).1)
        subst post
        subst r
        exact heapByteEff_storeByte_return_fresh he addr value typed v ha hc
      | none =>
        rw [evaluateHOLFiniteState_seq_line780] at hc
        rcases hb : evaluateHOLFiniteState mid (.storeByte addr value) with ⟨rb, mb⟩
        rw [hb] at hc
        cases rb with
        | some rb => simp at hc
        | none =>
          dsimp only at hc
          rw [evaluateHOLFiniteState_return] at hc
          split at hc <;> try cases hc
          split at hc <;> cases hc
  · cases hr

end PtxP34

namespace PtxP34
open WkBlockTxEnc

/-- The exact final conditional of `encode_receipt` preserves the entry frame;
the reserved byte before `start` is fresh and subtraction does not wrap. -/
theorem receipt_return_frame {F : Type}
    {s mid post : PanSemStateFiniteExact 64 F} {R : List Ivl} {gw : List String}
    (he : HeapByteEff s mid R gw) (start : BitVec 64) (v : ValueHOL 64)
    (hs : mid.locals.lookup (ofString "start") = some (.val (.word start)))
    (hfresh : globN s "heap_ptr" + 1 ≤ start.toNat ∧ start.toNat ≤ heapLimit)
    (hr : evaluateHOLFiniteState mid
      (.seq
        (.ite (.cmp .notEqual (.var .local (ofString "tx_type")) (.const 0))
          (.seq
            (.storeByte (.op .sub [.var .local (ofString "start"), .const 1])
              (.var .local (ofString "tx_type")))
            (.return (.rstruct
              [.op .sub [.var .local (ofString "start"), .const 1],
               .op .add [.var .local (ofString "w"), .const 1]]))) .skip)
        (.return (.rstruct [.var .local (ofString "start"), .var .local (ofString "w")]))) =
      (some (.returned v), post)) : HeapByteEff s post R gw := by
  apply heapByteEff_optional_prefix_return he _ _ _ _ _ v ?_ hr
  intro a ha
  have hev : @evalHOLExact 64 F _ mid.toExact
      (fun a => Classical.propDecidable (mid.memaddrs a))
      (.op .sub [.var .local (ofString "start"), .const 1]) =
      some (.val (.word (start - 1#64))) := by
    simp [evalHOLExact, evalListHOLExact, hs, wordOpHOL, wordOp, valueIsWord, valueWord]
  rw [hev] at ha
  have ha' : start - 1#64 = a := by
    exact HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj ha))
  subst a
  have hn : (start - 1#64).toNat = start.toNat - 1 := by
    rw [BitVec.toNat_sub]
    simp only [show (1#64 : BitVec 64).toNat = 1 from rfl]
    omega
  rw [hn]
  constructor <;> omega

end PtxP34

namespace PtxP34
open WkBlockTxEnc

/-- List finalization retains the `start` lookup needed to frame the receipt's
optional type-prefix write in the following return conditional. -/
theorem receipt_finish_preserves_start {F : Type}
    {s mid post : PanSemStateFiniteExact 64 F} {R : List Ivl} {gw : List String}
    (he : HeapByteEff s mid R gw) (start pend old : BitVec 64)
    (hs : mid.locals.lookup (ofString "start") = some (.val (.word start)))
    (hp : mid.locals.lookup (ofString "p") = some (.val (.word pend)))
    (hw : mid.locals.lookup (ofString "w") = some (.val (.word old)))
    (hle : start.toNat + 9 ≤ pend.toNat)
    (hfresh : globN s "heap_ptr" ≤ start.toNat ∧ pend.toNat ≤ heapLimit)
    (hr : evaluateHOLFiniteState mid
      (.call (some (some (.local, ofString "w"), none)) (ofString "rlp_finish_list")
        [.var .local (ofString "start"), .var .local (ofString "p")]) = (none, post)) :
    HeapByteEff s post R gw ∧
    post.locals.lookup (ofString "start") = some (.val (.word start)) := by
  have ht := eval_call_local_rlp_finish_list mid "w"
    (.var .local (ofString "start")) (.var .local (ofString "p")) start pend
    (R ++ [(start.toNat, pend.toNat - start.toNat)]) gw he.arena.1.code he.arena
    ⟨old, hw⟩ hs hp hle (le_trans hfresh.2 (by decide))
    ⟨(start.toNat, pend.toNat - start.toNat), List.mem_append_right _ (by simp),
      le_rfl, by omega⟩ (by rw [hr]; simp)
  rw [hr] at ht
  obtain ⟨w, _, _, _, hloc, heff⟩ := ht.1 rfl
  refine ⟨heapByteEff_trans_fresh he heff ?_, ?_⟩
  · intro i hi
    simp only [List.mem_singleton] at hi
    subst i
    exact ⟨hfresh.1, by dsimp; omega⟩
  · rw [hloc]
    simpa [HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "w" ≠ ofString "start" by decide] using hs

end PtxP34

namespace PtxP34
open WkBlockTxEnc
open private WkBlockTxEnc.call_noexc_ne_returned
  from InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.EncodeReceipt

/-- Compose list finalization with both concrete receipt return paths. -/
theorem receipt_finish_return_frame {F : Type}
    {s mid post : PanSemStateFiniteExact 64 F} {R : List Ivl} {gw : List String}
    (he : HeapByteEff s mid R gw) (start pend old : BitVec 64) (v : ValueHOL 64)
    (hs : mid.locals.lookup (ofString "start") = some (.val (.word start)))
    (hp : mid.locals.lookup (ofString "p") = some (.val (.word pend)))
    (hw : mid.locals.lookup (ofString "w") = some (.val (.word old)))
    (hle : start.toNat + 9 ≤ pend.toNat)
    (hfresh : globN s "heap_ptr" + 1 ≤ start.toNat ∧ pend.toNat ≤ heapLimit)
    (hr : evaluateHOLFiniteState mid
      (.seq
        (.call (some (some (.local, ofString "w"), none)) (ofString "rlp_finish_list")
          [.var .local (ofString "start"), .var .local (ofString "p")])
        (.seq
          (.ite (.cmp .notEqual (.var .local (ofString "tx_type")) (.const 0))
            (.seq
              (.storeByte (.op .sub [.var .local (ofString "start"), .const 1])
                (.var .local (ofString "tx_type")))
              (.return (.rstruct
                [.op .sub [.var .local (ofString "start"), .const 1],
                 .op .add [.var .local (ofString "w"), .const 1]]))) .skip)
          (.return (.rstruct [.var .local (ofString "start"), .var .local (ofString "w")])))) =
      (some (.returned v), post)) : HeapByteEff s post R gw := by
  rw [evaluateHOLFiniteState_seq_line780] at hr
  rcases hc : evaluateHOLFiniteState mid
      (.call (some (some (.local, ofString "w"), none)) (ofString "rlp_finish_list")
        [.var .local (ofString "start"), .var .local (ofString "p")]) with ⟨r, next⟩
  rw [hc] at hr
  cases r with
  | none =>
    obtain ⟨he', hs'⟩ := receipt_finish_preserves_start he start pend old hs hp hw hle
      ⟨by omega, hfresh.2⟩ hc
    exact receipt_return_frame he' start v hs' ⟨hfresh.1, by omega⟩ hr
  | some r =>
    have hn := WkBlockTxEnc.call_noexc_ne_returned mid (some (.local, ofString "w"))
      (ofString "rlp_finish_list") [.var .local (ofString "start"), .var .local (ofString "p")] v
    exact False.elim (hn (by simpa [hc] using congrArg Prod.fst hr))

end PtxP34

namespace PtxP34
open WkBlockTxEnc

/-- Advance the final receipt cursor before list finalization and return. -/
theorem receipt_advance_finish_return_frame {F : Type}
    {s mid post : PanSemStateFiniteExact 64 F} {R : List Ivl} {gw : List String}
    (he : HeapByteEff s mid R gw) (start p w : BitVec 64) (v : ValueHOL 64)
    (hs : mid.locals.lookup (ofString "start") = some (.val (.word start)))
    (hp : mid.locals.lookup (ofString "p") = some (.val (.word p)))
    (hw : mid.locals.lookup (ofString "w") = some (.val (.word w)))
    (hle : start.toNat + 9 ≤ p.toNat)
    (hfresh : globN s "heap_ptr" + 1 ≤ start.toNat ∧ p.toNat + w.toNat ≤ heapLimit)
    (hr : evaluateHOLFiniteState mid
      (.seq
        (.assign .local (ofString "p")
          (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
        (.seq
          (.call (some (some (.local, ofString "w"), none)) (ofString "rlp_finish_list")
            [.var .local (ofString "start"), .var .local (ofString "p")])
          (.seq
            (.ite (.cmp .notEqual (.var .local (ofString "tx_type")) (.const 0))
              (.seq
                (.storeByte (.op .sub [.var .local (ofString "start"), .const 1])
                  (.var .local (ofString "tx_type")))
                (.return (.rstruct
                  [.op .sub [.var .local (ofString "start"), .const 1],
                   .op .add [.var .local (ofString "w"), .const 1]]))) .skip)
            (.return (.rstruct [.var .local (ofString "start"), .var .local (ofString "w")]))))) =
      (some (.returned v), post)) : HeapByteEff s post R gw := by
  have hn : (p + w).toNat = p.toNat + w.toNat := by
    rw [BitVec.toNat_add]
    exact Nat.mod_eq_of_lt (lt_of_le_of_lt hfresh.2 (by decide))
  have ha : evaluateHOLFiniteState mid
      (.assign .local (ofString "p")
        (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])) =
      (none, setVarHOLFinite (ofString "p") (.val (.word (p + w))) mid) := by
    rw [evaluateHOLFiniteState_assign]
    have hev : @evalHOLExact 64 F _ mid.toExact
        (fun a => Classical.propDecidable (mid.memaddrs a))
        (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]) =
        some (.val (.word (p + w))) := by
      simp [evalHOLExact, evalListHOLExact, hp, hw, wordOpHOL, wordOp, valueIsWord, valueWord]
    have hv : mid.isValidValueHOLFinite .local (ofString "p") (.val (.word (p + w))) = true := by
      simp [PanSemStateFiniteExact.isValidValueHOLFinite, lookupKvarHOLExact, hp,
        shapeOfHOLExact, shapeEqHOL]
    rw [hev]
    dsimp only
    rw [if_pos hv]
    rfl
  rw [evaluateHOLFiniteState_seq_line780, ha] at hr
  let next := setVarHOLFinite (ofString "p") (.val (.word (p + w))) mid
  apply receipt_finish_return_frame (he.locals_clock next.locals next.clock) start (p + w) w v
  · simpa [next, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "p" ≠ ofString "start" by decide] using hs
  · simp [next, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  · simpa [next, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "p" ≠ ofString "w" by decide] using hw
  · rw [hn]; omega
  · exact ⟨hfresh.1, hn ▸ hfresh.2⟩
  · exact hr

end PtxP34

namespace PtxP34
open WkBlockTxEnc
open private WkBlockTxEnc.receiptKeccakIvls WkBlockTxEnc.logsEncodedSum
  WkBlockTxEnc.call_noexc_ne_returned
  from InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.EncodeReceipt

/-- Encode logs, advance the cursor, finalize the list, and return the receipt. -/
theorem receipt_logs_finish_return_frame {F : Type}
    {s mid post : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) (hma : s.memaddrs = ordinaryDomain)
    (he : HeapByteEff s mid (WkBlockTxEnc.receiptKeccakIvls s) ["heap_ptr"])
    (start p logs old : BitVec 64) (bound : Nat) (v : ValueHOL 64)
    (hs : mid.locals.lookup (ofString "start") = some (.val (.word start)))
    (hp : mid.locals.lookup (ofString "p") = some (.val (.word p)))
    (hl : mid.locals.lookup (ofString "logs") = some (.val (.word logs)))
    (hw : mid.locals.lookup (ofString "w") = some (.val (.word old)))
    (hle : start.toNat + 9 ≤ p.toNat)
    (hfresh : globN s "heap_ptr" + 1 ≤ start.toNat ∧ p.toNat + bound ≤ heapLimit)
    (hnz : logs.toNat ≠ 0) (hL : LogsListOK s logs.toNat) (hD : LogsDisjFixed s logs.toNat)
    (hfit : 9 + WkBlockTxEnc.logsEncodedSum s (memW s logs.toNat)
      (memW s (logs.toNat + 8)) ≤ bound)
    (hr : evaluateHOLFiniteState mid
      (.seq
        (.call (some (some (.local, ofString "w"), none)) (ofString "encode_logs")
          [.var .local (ofString "p"), .var .local (ofString "logs")])
        (.seq
          (.assign .local (ofString "p")
            (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
          (.seq
            (.call (some (some (.local, ofString "w"), none)) (ofString "rlp_finish_list")
              [.var .local (ofString "start"), .var .local (ofString "p")])
            (.seq
              (.ite (.cmp .notEqual (.var .local (ofString "tx_type")) (.const 0))
                (.seq
                  (.storeByte (.op .sub [.var .local (ofString "start"), .const 1])
                    (.var .local (ofString "tx_type")))
                  (.return (.rstruct
                    [.op .sub [.var .local (ofString "start"), .const 1],
                     .op .add [.var .local (ofString "w"), .const 1]]))) .skip)
              (.return (.rstruct [.var .local (ofString "start"), .var .local (ofString "w")])))))) =
      (some (.returned v), post)) :
    HeapByteEff s post (WkBlockTxEnc.receiptKeccakIvls s) ["heap_ptr"] := by
  rw [evaluateHOLFiniteState_seq_line780] at hr
  rcases hc : evaluateHOLFiniteState mid
      (.call (some (some (.local, ofString "w"), none)) (ofString "encode_logs")
        [.var .local (ofString "p"), .var .local (ofString "logs")]) with ⟨r, next⟩
  rw [hc] at hr
  cases r with
  | none =>
    obtain ⟨he', w, hb, _, hloc⟩ := receipt_encode_logs_frame_result hA hma he "w"
      (.var .local (ofString "p")) (.var .local (ofString "logs")) p logs bound
      ⟨by omega, hfresh.2⟩ hnz hL hD hfit ⟨old, hw⟩ hp hl hc
    apply receipt_advance_finish_return_frame he' start p w v
    · rw [hloc]
      simpa [HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "w" ≠ ofString "start" by decide] using hs
    · rw [hloc]
      simpa [HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "w" ≠ ofString "p" by decide] using hp
    · rw [hloc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    · exact hle
    · exact ⟨hfresh.1, by omega⟩
    · exact hr
  | some r =>
    have hn := WkBlockTxEnc.call_noexc_ne_returned mid (some (.local, ofString "w"))
      (ofString "encode_logs") [.var .local (ofString "p"), .var .local (ofString "logs")] v
    exact False.elim (hn (by simpa [hc] using congrArg Prod.fst hr))

end PtxP34

namespace PtxP34
open WkBlockTxEnc

/-- A receipt cursor increment transports the frame and every other local to
the continuation, including when the continuation returns from the receipt. -/
theorem receipt_cursor_continuation_frame {F : Type}
    {s mid post : PanSemStateFiniteExact 64 F} {R : List Ivl} {gw : List String}
    (he : HeapByteEff s mid R gw) (p w : BitVec 64)
    (hp : mid.locals.lookup (ofString "p") = some (.val (.word p)))
    (hw : mid.locals.lookup (ofString "w") = some (.val (.word w)))
    (tail : ProgHOL 64) (v : ValueHOL 64)
    (hcont : ∀ next : PanSemStateFiniteExact 64 F,
      HeapByteEff s next R gw →
      next.locals.lookup (ofString "p") = some (.val (.word (p + w))) →
      (∀ name, name ≠ ofString "p" → next.locals.lookup name = mid.locals.lookup name) →
      evaluateHOLFiniteState next tail = (some (.returned v), post) →
      HeapByteEff s post R gw)
    (hr : evaluateHOLFiniteState mid
      (.seq (.assign .local (ofString "p")
        (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])) tail) =
      (some (.returned v), post)) : HeapByteEff s post R gw := by
  have ha : evaluateHOLFiniteState mid
      (.assign .local (ofString "p")
        (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])) =
      (none, setVarHOLFinite (ofString "p") (.val (.word (p + w))) mid) := by
    rw [evaluateHOLFiniteState_assign]
    have hev : @evalHOLExact 64 F _ mid.toExact
        (fun a => Classical.propDecidable (mid.memaddrs a))
        (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]) =
        some (.val (.word (p + w))) := by
      simp [evalHOLExact, evalListHOLExact, hp, hw, wordOpHOL, wordOp, valueIsWord, valueWord]
    have hv : mid.isValidValueHOLFinite .local (ofString "p") (.val (.word (p + w))) = true := by
      simp [PanSemStateFiniteExact.isValidValueHOLFinite, lookupKvarHOLExact, hp,
        shapeOfHOLExact, shapeEqHOL]
    rw [hev]
    dsimp only
    rw [if_pos hv]
    rfl
  rw [evaluateHOLFiniteState_seq_line780, ha] at hr
  let next := setVarHOLFinite (ofString "p") (.val (.word (p + w))) mid
  apply hcont next (he.locals_clock next.locals next.clock) ?_ ?_ hr
  · simp [next, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  · intro name hn
    simp [next, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hn]

end PtxP34

namespace PtxP34
open WkBlockTxEnc
open private WkBlockTxEnc.receiptKeccakIvls WkBlockTxEnc.logsEncodedSum
  from InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.EncodeReceipt

/-- The post-bloom cursor advance composes with log encoding and receipt return. -/
theorem receipt_advance_logs_finish_return_frame {F : Type}
    {s mid post : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) (hma : s.memaddrs = ordinaryDomain)
    (he : HeapByteEff s mid (WkBlockTxEnc.receiptKeccakIvls s) ["heap_ptr"])
    (start p logs w : BitVec 64) (bound : Nat) (v : ValueHOL 64)
    (hs : mid.locals.lookup (ofString "start") = some (.val (.word start)))
    (hp : mid.locals.lookup (ofString "p") = some (.val (.word p)))
    (hl : mid.locals.lookup (ofString "logs") = some (.val (.word logs)))
    (hw : mid.locals.lookup (ofString "w") = some (.val (.word w)))
    (hle : start.toNat + 9 ≤ p.toNat)
    (hfresh : globN s "heap_ptr" + 1 ≤ start.toNat ∧ p.toNat + w.toNat + bound ≤ heapLimit)
    (hnz : logs.toNat ≠ 0) (hL : LogsListOK s logs.toNat) (hD : LogsDisjFixed s logs.toNat)
    (hfit : 9 + WkBlockTxEnc.logsEncodedSum s (memW s logs.toNat)
      (memW s (logs.toNat + 8)) ≤ bound)
    (hr : evaluateHOLFiniteState mid
      (.seq
        (.assign .local (ofString "p")
          (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
        (.seq
          (.call (some (some (.local, ofString "w"), none)) (ofString "encode_logs")
            [.var .local (ofString "p"), .var .local (ofString "logs")])
          (.seq
            (.assign .local (ofString "p")
              (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
            (.seq
              (.call (some (some (.local, ofString "w"), none)) (ofString "rlp_finish_list")
                [.var .local (ofString "start"), .var .local (ofString "p")])
              (.seq
                (.ite (.cmp .notEqual (.var .local (ofString "tx_type")) (.const 0))
                  (.seq
                    (.storeByte (.op .sub [.var .local (ofString "start"), .const 1])
                      (.var .local (ofString "tx_type")))
                    (.return (.rstruct
                      [.op .sub [.var .local (ofString "start"), .const 1],
                       .op .add [.var .local (ofString "w"), .const 1]]))) .skip)
                (.return (.rstruct [.var .local (ofString "start"), .var .local (ofString "w")]))))))) =
      (some (.returned v), post)) :
    HeapByteEff s post (WkBlockTxEnc.receiptKeccakIvls s) ["heap_ptr"] := by
  have hn : (p + w).toNat = p.toNat + w.toNat := by
    rw [BitVec.toNat_add]
    apply Nat.mod_eq_of_lt
    have hlim : heapLimit < 2 ^ 64 := by decide
    omega
  apply receipt_cursor_continuation_frame he p w hp hw _ v ?_ hr
  intro next he' hp' hloc hr'
  apply receipt_logs_finish_return_frame hA hma he' start (p + w) logs w bound v
  · rw [hloc _ (by decide)]; exact hs
  · exact hp'
  · rw [hloc _ (by decide)]; exact hl
  · rw [hloc _ (by decide)]; exact hw
  · rw [hn]; omega
  · exact ⟨hfresh.1, by rw [hn]; exact hfresh.2⟩
  · exact hnz
  · exact hL
  · exact hD
  · exact hfit
  · exact hr'

end PtxP34

namespace PtxP34
open WkBlockTxEnc
open private WkBlockTxEnc.receiptKeccakIvls WkBlockTxEnc.logsEncodedSum
  WkBlockTxEnc.call_noexc_ne_returned
  from InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.EncodeReceipt

/-- The complete bloom-to-return receipt suffix preserves the entry frame. -/
theorem receipt_bloom_logs_finish_return_frame {F : Type}
    {s mid post : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) (hma : s.memaddrs = ordinaryDomain)
    (he : HeapByteEff s mid (WkBlockTxEnc.receiptKeccakIvls s) ["heap_ptr"])
    (start p logs bloom old : BitVec 64) (bound : Nat) (v : ValueHOL 64)
    (hs : mid.locals.lookup (ofString "start") = some (.val (.word start)))
    (hp : mid.locals.lookup (ofString "p") = some (.val (.word p)))
    (hl : mid.locals.lookup (ofString "logs") = some (.val (.word logs)))
    (hb : mid.locals.lookup (ofString "bloom") = some (.val (.word bloom)))
    (hw : mid.locals.lookup (ofString "w") = some (.val (.word old)))
    (hle : start.toNat + 9 ≤ p.toNat)
    (hfresh : globN s "heap_ptr" + 1 ≤ start.toNat ∧ p.toNat + 265 + bound ≤ heapLimit)
    (hbf : globN s "heap_ptr" ≤ bloom.toNat ∧ bloom.toNat + 256 ≤ heapLimit)
    (hnz : logs.toNat ≠ 0) (hL : LogsListOK s logs.toNat) (hD : LogsDisjFixed s logs.toNat)
    (hfit : 9 + WkBlockTxEnc.logsEncodedSum s (memW s logs.toNat)
      (memW s (logs.toNat + 8)) ≤ bound)
    (hr : evaluateHOLFiniteState mid
      (.seq
        (.call (some (none, none)) (ofString "logs_bloom")
          [.var .local (ofString "logs"), .var .local (ofString "bloom")])
        (.seq
          (.call (some (some (.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
            [.var .local (ofString "p"), .var .local (ofString "bloom"), .const 256])
          (.seq
            (.assign .local (ofString "p")
              (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
            (.seq
              (.call (some (some (.local, ofString "w"), none)) (ofString "encode_logs")
                [.var .local (ofString "p"), .var .local (ofString "logs")])
              (.seq
                (.assign .local (ofString "p")
                  (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                (.seq
                  (.call (some (some (.local, ofString "w"), none)) (ofString "rlp_finish_list")
                    [.var .local (ofString "start"), .var .local (ofString "p")])
                  (.seq
                    (.ite (.cmp .notEqual (.var .local (ofString "tx_type")) (.const 0))
                      (.seq
                        (.storeByte (.op .sub [.var .local (ofString "start"), .const 1])
                          (.var .local (ofString "tx_type")))
                        (.return (.rstruct
                          [.op .sub [.var .local (ofString "start"), .const 1],
                           .op .add [.var .local (ofString "w"), .const 1]]))) .skip)
                    (.return (.rstruct [.var .local (ofString "start"), .var .local (ofString "w")]))))))))) =
      (some (.returned v), post)) :
    HeapByteEff s post (WkBlockTxEnc.receiptKeccakIvls s) ["heap_ptr"] := by
  rw [← evaluate_seq_assoc] at hr
  have hn := seq_not_returned mid
    (.call (some (none, none)) (ofString "logs_bloom")
      [.var .local (ofString "logs"), .var .local (ofString "bloom")])
    (.call (some (some (.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
      [.var .local (ofString "p"), .var .local (ofString "bloom"), .const 256]) v
    (ignored_call_not_returned mid _ _ v)
    (fun next => WkBlockTxEnc.call_noexc_ne_returned next _ _ _ v)
  obtain ⟨next, hc, ht⟩ := seq_returned_of_not_returned hn hr
  obtain ⟨he', w, hwb, hloc⟩ := receipt_bloom_encode_frame he logs bloom p old hl hb hp hw
    hbf ⟨by omega, by omega⟩ hc
  apply receipt_advance_logs_finish_return_frame hA hma he' start p logs w bound v
  · rw [hloc]
    simpa [HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "w" ≠ ofString "start" by decide] using hs
  · rw [hloc]
    simpa [HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "w" ≠ ofString "p" by decide] using hp
  · rw [hloc]
    simpa [HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "w" ≠ ofString "logs" by decide] using hl
  · rw [hloc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  · exact hle
  · exact ⟨hfresh.1, by omega⟩
  · exact hnz
  · exact hL
  · exact hD
  · exact hfit
  · exact ht

end PtxP34

namespace PtxP34
open WkBlockTxEnc

/-- Gas serialization preserves the receipt frame and exposes its bounded
encoded length together with the exact caller-local update. -/
theorem receipt_gas_encode_frame {F : Type}
    {s mid post : PanSemStateFiniteExact 64 F} {R : List Ivl} {gw : List String}
    (he : HeapByteEff s mid R gw) (p gas old : BitVec 64)
    (hp : mid.locals.lookup (ofString "p") = some (.val (.word p)))
    (hg : mid.locals.lookup (ofString "cumulative_gas") = some (.val (.word gas)))
    (hw : mid.locals.lookup (ofString "w") = some (.val (.word old)))
    (hfresh : globN s "heap_ptr" ≤ p.toNat ∧ p.toNat + 9 ≤ heapLimit)
    (hr : evaluateHOLFiniteState mid
      (.call (some (some (.local, ofString "w"), none)) (ofString "rlp_encode_word")
        [.var .local (ofString "p"), .var .local (ofString "cumulative_gas")]) = (none, post)) :
    HeapByteEff s post R gw ∧ ∃ w : BitVec 64, 1 ≤ w.toNat ∧ w.toNat ≤ 9 ∧
      post.locals = mid.locals.update (ofString "w", .val (.word w)) := by
  have ht := eval_call_local_rlp_encode_word mid "w"
    (.var .local (ofString "p")) (.var .local (ofString "cumulative_gas")) p gas
    (R ++ [(p.toNat, 9)]) gw he.arena.1.code he.arena ⟨old, hw⟩ hp hg
    ⟨(p.toNat, 9), List.mem_append_right _ (by simp), le_rfl, le_rfl⟩
    (by rw [hr]; simp)
  rw [hr] at ht
  obtain ⟨w, hlo, hhi, _, _, hloc, heff⟩ := ht.1 rfl
  refine ⟨heapByteEff_trans_fresh he heff ?_, w, hlo, hhi, hloc⟩
  intro i hi
  simp only [List.mem_singleton] at hi
  subst i
  exact hfresh

end PtxP34

namespace PtxP34
open WkBlockTxEnc
open private WkBlockTxEnc.call_noexc_ne_returned
  from InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.EncodeReceipt

/-- Carry gas encoding's bounded result and preserved locals into the receipt
continuation, ruling out a premature return from the encoding call. -/
theorem receipt_gas_continuation_frame {F : Type}
    {s mid post : PanSemStateFiniteExact 64 F} {R : List Ivl} {gw : List String}
    (he : HeapByteEff s mid R gw) (p gas old : BitVec 64)
    (hp : mid.locals.lookup (ofString "p") = some (.val (.word p)))
    (hg : mid.locals.lookup (ofString "cumulative_gas") = some (.val (.word gas)))
    (hw : mid.locals.lookup (ofString "w") = some (.val (.word old)))
    (hfresh : globN s "heap_ptr" ≤ p.toNat ∧ p.toNat + 9 ≤ heapLimit)
    (tail : ProgHOL 64) (v : ValueHOL 64)
    (hcont : ∀ (next : PanSemStateFiniteExact 64 F) (w : BitVec 64),
      HeapByteEff s next R gw → 1 ≤ w.toNat → w.toNat ≤ 9 →
      next.locals = mid.locals.update (ofString "w", .val (.word w)) →
      evaluateHOLFiniteState next tail = (some (.returned v), post) →
      HeapByteEff s post R gw)
    (hr : evaluateHOLFiniteState mid
      (.seq (.call (some (some (.local, ofString "w"), none)) (ofString "rlp_encode_word")
        [.var .local (ofString "p"), .var .local (ofString "cumulative_gas")]) tail) =
      (some (.returned v), post)) : HeapByteEff s post R gw := by
  obtain ⟨next, hc, ht⟩ := seq_returned_of_not_returned
    (WkBlockTxEnc.call_noexc_ne_returned mid (some (.local, ofString "w"))
      (ofString "rlp_encode_word")
      [.var .local (ofString "p"), .var .local (ofString "cumulative_gas")] v) hr
  obtain ⟨he', w, hlo, hhi, hloc⟩ := receipt_gas_encode_frame he p gas old hp hg hw hfresh hc
  exact hcont next w he' hlo hhi hloc ht

end PtxP34

namespace PtxP34
open WkBlockTxEnc

/-- Bloom allocation supplies fresh bounded storage to a returning continuation;
restoring its scoped local does not change the receipt frame. -/
theorem receipt_bloom_alloc_continuation_frame {F : Type}
    {s mid post : PanSemStateFiniteExact 64 F} {R : List Ivl}
    (he : HeapByteEff s mid R ["heap_ptr"])
    (tail : ProgHOL 64) (v : ValueHOL 64)
    (hcont : ∀ (next final : PanSemStateFiniteExact 64 F) (bloom : BitVec 64),
      HeapByteEff s next R ["heap_ptr"] →
      globN s "heap_ptr" ≤ bloom.toNat → bloom.toNat + 256 ≤ heapLimit →
      next.locals = mid.locals.update (ofString "bloom", .val (.word bloom)) →
      evaluateHOLFiniteState next tail = (some (.returned v), final) →
      HeapByteEff s final R ["heap_ptr"])
    (hr : evaluateHOLFiniteState mid
      (.decCall (ofString "bloom") .one (ofString "alloc") [.const 256] tail) =
      (some (.returned v), post)) : HeapByteEff s post R ["heap_ptr"] := by
  obtain ⟨bloom, n, q, next, hn, hb, _, _, hfit, hlim, _, _, _, _, hloc,
      he', _, _, hrun⟩ := eval_decCall_alloc_resumes mid "bloom" (.const 256) tail
        R ["heap_ptr"] he.arena.1.code he.arena (by simp)
        (by rw [hr]; simp) (by rw [hr]; exact Or.inl ⟨v, rfl⟩)
  have hn' : n = 256#64 := by simpa [evalHOLExact] using hn.symm
  subst n
  have hret : (evaluateHOLFiniteState next tail).1 = some (.returned v) := by
    rw [hr] at hrun
    exact (congrArg Prod.fst hrun).symm
  have hf := hcont next (evaluateHOLFiniteState next tail).2 bloom (he.trans he')
    (by rw [hb]; exact he.hp_le) (by change bloom.toNat + 256 ≤ q.toNat at hfit; omega)
    hloc (Prod.ext hret rfl)
  rw [hr] at hrun
  have hp := congrArg Prod.snd hrun
  dsimp only at hp
  rw [hp]
  exact hf.locals_clock _ _

end PtxP34

namespace PtxP34
open WkBlockTxEnc

/-- Gas encoding and cursor advancement expose a bounded, non-wrapping cursor
to the bloom allocation continuation. -/
theorem receipt_gas_advance_continuation_frame {F : Type}
    {s mid post : PanSemStateFiniteExact 64 F} {R : List Ivl} {gw : List String}
    (he : HeapByteEff s mid R gw) (p gas old : BitVec 64)
    (hp : mid.locals.lookup (ofString "p") = some (.val (.word p)))
    (hg : mid.locals.lookup (ofString "cumulative_gas") = some (.val (.word gas)))
    (hw : mid.locals.lookup (ofString "w") = some (.val (.word old)))
    (hfresh : globN s "heap_ptr" ≤ p.toNat ∧ p.toNat + 9 ≤ heapLimit)
    (tail : ProgHOL 64) (v : ValueHOL 64)
    (hcont : ∀ (next : PanSemStateFiniteExact 64 F) (q w : BitVec 64),
      HeapByteEff s next R gw → p.toNat + 1 ≤ q.toNat → q.toNat ≤ p.toNat + 9 →
      next.locals.lookup (ofString "p") = some (.val (.word q)) →
      next.locals.lookup (ofString "w") = some (.val (.word w)) →
      (∀ name, name ≠ ofString "p" → name ≠ ofString "w" →
        next.locals.lookup name = mid.locals.lookup name) →
      evaluateHOLFiniteState next tail = (some (.returned v), post) → HeapByteEff s post R gw)
    (hr : evaluateHOLFiniteState mid
      (.seq (.call (some (some (.local, ofString "w"), none)) (ofString "rlp_encode_word")
        [.var .local (ofString "p"), .var .local (ofString "cumulative_gas")])
        (.seq (.assign .local (ofString "p")
          (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])) tail)) =
      (some (.returned v), post)) : HeapByteEff s post R gw := by
  apply receipt_gas_continuation_frame he p gas old hp hg hw hfresh _ v ?_ hr
  intro next w he' hlo hhi hloc hr'
  have hp' : next.locals.lookup (ofString "p") = some (.val (.word p)) := by
    rw [hloc]
    simpa [HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "w" ≠ ofString "p" by decide] using hp
  have hw' : next.locals.lookup (ofString "w") = some (.val (.word w)) := by
    rw [hloc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hn : (p + w).toNat = p.toNat + w.toNat := by
    rw [BitVec.toNat_add]
    apply Nat.mod_eq_of_lt
    have hlim : heapLimit < 2 ^ 64 := by decide
    omega
  apply receipt_cursor_continuation_frame he' p w hp' hw' tail v ?_ hr'
  intro final he'' hp'' hkeep hr''
  apply hcont final (p + w) w he'' (by rw [hn]; omega) (by rw [hn]; omega) hp''
  · rw [hkeep _ (by decide)]; exact hw'
  · intro name hnp hnw
    rw [hkeep name hnp, hloc]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hnw]
  · exact hr''

end PtxP34

namespace PtxP34
open WkBlockTxEnc
open private WkBlockTxEnc.receiptKeccakIvls WkBlockTxEnc.logsEncodedSum
  from InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.EncodeReceipt

/-- Allocating the bloom and executing the complete receipt suffix preserves
the entry frame, including restoration of the scoped bloom local. -/
theorem receipt_alloc_bloom_return_frame {F : Type}
    {s mid post : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) (hma : s.memaddrs = ordinaryDomain)
    (he : HeapByteEff s mid (WkBlockTxEnc.receiptKeccakIvls s) ["heap_ptr"])
    (start p logs old : BitVec 64) (bound : Nat) (v : ValueHOL 64)
    (hs : mid.locals.lookup (ofString "start") = some (.val (.word start)))
    (hp : mid.locals.lookup (ofString "p") = some (.val (.word p)))
    (hl : mid.locals.lookup (ofString "logs") = some (.val (.word logs)))
    (hw : mid.locals.lookup (ofString "w") = some (.val (.word old)))
    (hle : start.toNat + 9 ≤ p.toNat)
    (hfresh : globN s "heap_ptr" + 1 ≤ start.toNat ∧ p.toNat + 265 + bound ≤ heapLimit)
    (hnz : logs.toNat ≠ 0) (hL : LogsListOK s logs.toNat) (hD : LogsDisjFixed s logs.toNat)
    (hfit : 9 + WkBlockTxEnc.logsEncodedSum s (memW s logs.toNat)
      (memW s (logs.toNat + 8)) ≤ bound)
    (hr : evaluateHOLFiniteState mid
      (.decCall (ofString "bloom") .one (ofString "alloc") [.const 256]
        (.seq
          (.call (some (none, none)) (ofString "logs_bloom")
            [.var .local (ofString "logs"), .var .local (ofString "bloom")])
          (.seq
            (.call (some (some (.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
              [.var .local (ofString "p"), .var .local (ofString "bloom"), .const 256])
            (.seq
              (.assign .local (ofString "p")
                (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
              (.seq
                (.call (some (some (.local, ofString "w"), none)) (ofString "encode_logs")
                  [.var .local (ofString "p"), .var .local (ofString "logs")])
                (.seq
                  (.assign .local (ofString "p")
                    (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                  (.seq
                    (.call (some (some (.local, ofString "w"), none)) (ofString "rlp_finish_list")
                      [.var .local (ofString "start"), .var .local (ofString "p")])
                    (.seq
                      (.ite (.cmp .notEqual (.var .local (ofString "tx_type")) (.const 0))
                        (.seq
                          (.storeByte (.op .sub [.var .local (ofString "start"), .const 1])
                            (.var .local (ofString "tx_type")))
                          (.return (.rstruct
                            [.op .sub [.var .local (ofString "start"), .const 1],
                             .op .add [.var .local (ofString "w"), .const 1]]))) .skip)
                      (.return (.rstruct [.var .local (ofString "start"), .var .local (ofString "w")])))))))))) =
      (some (.returned v), post)) :
    HeapByteEff s post (WkBlockTxEnc.receiptKeccakIvls s) ["heap_ptr"] := by
  apply receipt_bloom_alloc_continuation_frame he _ v ?_ hr
  intro next final bloom he' hb0 hb1 hloc hr'
  apply receipt_bloom_logs_finish_return_frame hA hma he' start p logs bloom old bound v
  · rw [hloc]
    simpa [HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "bloom" ≠ ofString "start" by decide] using hs
  · rw [hloc]
    simpa [HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "bloom" ≠ ofString "p" by decide] using hp
  · rw [hloc]
    simpa [HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "bloom" ≠ ofString "logs" by decide] using hl
  · rw [hloc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  · rw [hloc]
    simpa [HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "bloom" ≠ ofString "w" by decide] using hw
  · exact hle
  · exact hfresh
  · exact ⟨hb0, hb1⟩
  · exact hnz
  · exact hL
  · exact hD
  · exact hfit
  · exact hr'

end PtxP34

namespace PtxP34
open WkBlockTxEnc
open private WkBlockTxEnc.receiptKeccakIvls WkBlockTxEnc.logsEncodedSum
  from InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.EncodeReceipt

/-- The gas encoder, cursor advance, bloom allocation and concrete receipt
return suffix together preserve the entry heap frame. -/
theorem receipt_gas_alloc_bloom_return_frame {F : Type}
    {s mid post : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) (hma : s.memaddrs = ordinaryDomain)
    (he : HeapByteEff s mid (WkBlockTxEnc.receiptKeccakIvls s) ["heap_ptr"])
    (start p logs gas old : BitVec 64) (bound : Nat) (v : ValueHOL 64)
    (hs : mid.locals.lookup (ofString "start") = some (.val (.word start)))
    (hp : mid.locals.lookup (ofString "p") = some (.val (.word p)))
    (hl : mid.locals.lookup (ofString "logs") = some (.val (.word logs)))
    (hg : mid.locals.lookup (ofString "cumulative_gas") = some (.val (.word gas)))
    (hw : mid.locals.lookup (ofString "w") = some (.val (.word old)))
    (hle : start.toNat + 9 ≤ p.toNat)
    (hfresh : globN s "heap_ptr" + 1 ≤ start.toNat ∧ p.toNat + 274 + bound ≤ heapLimit)
    (hnz : logs.toNat ≠ 0) (hL : LogsListOK s logs.toNat) (hD : LogsDisjFixed s logs.toNat)
    (hfit : 9 + WkBlockTxEnc.logsEncodedSum s (memW s logs.toNat)
      (memW s (logs.toNat + 8)) ≤ bound)
    (hr : evaluateHOLFiniteState mid
      (.seq
        (.call (some (some (.local, ofString "w"), none)) (ofString "rlp_encode_word")
          [.var .local (ofString "p"), .var .local (ofString "cumulative_gas")])
        (.seq
          (.assign .local (ofString "p")
            (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
          (.decCall (ofString "bloom") .one (ofString "alloc") [.const 256]
            (.seq
              (.call (some (none, none)) (ofString "logs_bloom")
                [.var .local (ofString "logs"), .var .local (ofString "bloom")])
              (.seq
                (.call (some (some (.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
                  [.var .local (ofString "p"), .var .local (ofString "bloom"), .const 256])
                (.seq
                  (.assign .local (ofString "p")
                    (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                  (.seq
                    (.call (some (some (.local, ofString "w"), none)) (ofString "encode_logs")
                      [.var .local (ofString "p"), .var .local (ofString "logs")])
                    (.seq
                      (.assign .local (ofString "p")
                        (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                      (.seq
                        (.call (some (some (.local, ofString "w"), none)) (ofString "rlp_finish_list")
                          [.var .local (ofString "start"), .var .local (ofString "p")])
                        (.seq
                          (.ite (.cmp .notEqual (.var .local (ofString "tx_type")) (.const 0))
                            (.seq
                              (.storeByte (.op .sub [.var .local (ofString "start"), .const 1])
                                (.var .local (ofString "tx_type")))
                              (.return (.rstruct
                                [.op .sub [.var .local (ofString "start"), .const 1],
                                 .op .add [.var .local (ofString "w"), .const 1]]))) .skip)
                          (.return (.rstruct [.var .local (ofString "start"),
                            .var .local (ofString "w")])))))))))))) =
      (some (.returned v), post)) :
    HeapByteEff s post (WkBlockTxEnc.receiptKeccakIvls s) ["heap_ptr"] := by
  apply receipt_gas_advance_continuation_frame he p gas old hp hg hw
    ⟨by omega, by omega⟩ _ v ?_ hr
  intro next q w he' hlo hhi hp' hw' hkeep hr'
  apply receipt_alloc_bloom_return_frame hA hma he' start q logs w bound v
  · rw [hkeep _ (by decide) (by decide)]; exact hs
  · exact hp'
  · rw [hkeep _ (by decide) (by decide)]; exact hl
  · exact hw'
  · omega
  · exact ⟨hfresh.1, by omega⟩
  · exact hnz
  · exact hL
  · exact hD
  · exact hfit
  · exact hr'

end PtxP34

namespace PtxP34
open WkBlockTxEnc

/-- A successful fresh-byte store exposes its unchanged local environment to
the returning receipt continuation. -/
theorem receipt_storeByte_continuation_frame {F : Type}
    {s mid post : PanSemStateFiniteExact 64 F} {R : List Ivl} {gw : List String}
    (he : HeapByteEff s mid R gw) (addr value : ExpHOL 64)
    (haddr : ∀ a : BitVec 64,
      @evalHOLExact 64 F _ mid.toExact (fun a => Classical.propDecidable (mid.memaddrs a)) addr =
        some (.val (.word a)) →
      globN s "heap_ptr" ≤ a.toNat ∧ a.toNat + 1 ≤ heapLimit)
    (tail : ProgHOL 64) (v : ValueHOL 64)
    (hcont : ∀ next : PanSemStateFiniteExact 64 F,
      HeapByteEff s next R gw → next.locals = mid.locals →
      evaluateHOLFiniteState next tail = (some (.returned v), post) →
      HeapByteEff s post R gw)
    (hr : evaluateHOLFiniteState mid (.seq (.storeByte addr value) tail) =
      (some (.returned v), post)) : HeapByteEff s post R gw := by
  have hn : (evaluateHOLFiniteState mid (.storeByte addr value)).1 ≠
      some (.returned v) := by
    rw [evaluateHOLFiniteState_storeByte]
    split <;> try simp
    split <;> try simp
    split <;> simp
  obtain ⟨next, hc, ht⟩ := seq_returned_of_not_returned hn hr
  apply hcont next (heapByteEff_storeByte_fresh he addr value hc haddr) ?_ ht
  rw [evaluateHOLFiniteState_storeByte] at hc
  split at hc <;> try simp_all
  split at hc <;> try simp_all
  split at hc <;> simp_all
  exact (congrArg PanSemStateFiniteExact.locals hc).symm

end PtxP34

namespace PtxP34
open WkBlockTxEnc

/-- The status-byte branch writes one fresh byte and sets its encoded length
to one, preserving every other local for the gas continuation. -/
theorem receipt_status_branch_frame {F : Type}
    {s mid post : PanSemStateFiniteExact 64 F} {R : List Ivl} {gw : List String}
    (he : HeapByteEff s mid R gw) (p old byte : BitVec 64)
    (hp : mid.locals.lookup (ofString "p") = some (.val (.word p)))
    (hw : mid.locals.lookup (ofString "w") = some (.val (.word old)))
    (hfresh : globN s "heap_ptr" ≤ p.toNat ∧ p.toNat + 1 ≤ heapLimit)
    (tail : ProgHOL 64) (v : ValueHOL 64)
    (hcont : ∀ next : PanSemStateFiniteExact 64 F,
      HeapByteEff s next R gw →
      next.locals = mid.locals.update (ofString "w", .val (.word 1#64)) →
      evaluateHOLFiniteState next tail = (some (.returned v), post) →
      HeapByteEff s post R gw)
    (hr : evaluateHOLFiniteState mid
      (.seq (.seq (.storeByte (.var .local (ofString "p")) (.const byte))
        (.assign .local (ofString "w") (.const 1))) tail) =
      (some (.returned v), post)) : HeapByteEff s post R gw := by
  have hassoc : evaluateHOLFiniteState mid
      (.seq (.storeByte (.var .local (ofString "p")) (.const byte))
        (.seq (.assign .local (ofString "w") (.const 1)) tail)) =
      (some (.returned v), post) := by
    simp only [evaluateHOLFiniteState_seq_line780] at hr ⊢
    cases hx : (evaluateHOLFiniteState mid
      (.storeByte (.var .local (ofString "p")) (.const byte))).1 <;>
      simpa only [hx] using hr
  apply receipt_storeByte_continuation_frame he _ _ ?_ _ v ?_ hassoc
  · intro a ha
    have ha' : p = a := by simpa [evalHOLExact, hp] using ha
    subst a
    exact hfresh
  · intro next he' hloc ht
    have hw' : next.locals.lookup (ofString "w") = some (.val (.word old)) := by
      rw [hloc]; exact hw
    have hass : evaluateHOLFiniteState next (.assign .local (ofString "w") (.const 1)) =
        (none, setVarHOLFinite (ofString "w") (.val (.word 1#64)) next) := by
      rw [evaluateHOLFiniteState_assign]
      simp [evalHOLExact, PanSemStateFiniteExact.isValidValueHOLFinite,
        lookupKvarHOLExact, hw', shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite]
    rw [evaluateHOLFiniteState_seq_line780, hass] at ht
    exact hcont _ (he'.locals_clock _ _)
      (by simp [setVarHOLFinite, hloc]) ht

end PtxP34

namespace PtxP34
open WkBlockTxEnc

/-- Both receipt-status cases supply the same one-byte length and frame to
the rest of the encoder. -/
theorem receipt_status_continuation_frame {F : Type}
    {s mid post : PanSemStateFiniteExact 64 F} {R : List Ivl} {gw : List String}
    (he : HeapByteEff s mid R gw) (p old succeeded : BitVec 64)
    (hp : mid.locals.lookup (ofString "p") = some (.val (.word p)))
    (hw : mid.locals.lookup (ofString "w") = some (.val (.word old)))
    (hs : mid.locals.lookup (ofString "succeeded") = some (.val (.word succeeded)))
    (hfresh : globN s "heap_ptr" ≤ p.toNat ∧ p.toNat + 1 ≤ heapLimit)
    (tail : ProgHOL 64) (v : ValueHOL 64)
    (hcont : ∀ next : PanSemStateFiniteExact 64 F,
      HeapByteEff s next R gw →
      next.locals = mid.locals.update (ofString "w", .val (.word 1#64)) →
      evaluateHOLFiniteState next tail = (some (.returned v), post) →
      HeapByteEff s post R gw)
    (hr : evaluateHOLFiniteState mid
      (.seq
        (.ite (.cmp .notEqual (.var .local (ofString "succeeded")) (.const 0))
          (.seq (.storeByte (.var .local (ofString "p")) (.const 1))
            (.assign .local (ofString "w") (.const 1)))
          (.seq (.storeByte (.var .local (ofString "p")) (.const 128))
            (.assign .local (ofString "w") (.const 1)))) tail) =
      (some (.returned v), post)) : HeapByteEff s post R gw := by
  have hcond : @evalHOLExact 64 F _ mid.toExact
      (fun a => Classical.propDecidable (mid.memaddrs a))
      (.cmp .notEqual (.var .local (ofString "succeeded")) (.const 0)) =
      some (.val (.word (if succeeded ≠ 0#64 then 1#64 else 0#64))) := by
    simp only [evalHOLExact, hs, wordCmpHOL]
    by_cases hz : succeeded = 0#64 <;> simp [hz]
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite, hcond] at hr
  by_cases hz : succeeded = 0#64
  · simp only [hz, ne_eq, not_true_eq_false, if_false, if_pos (show (0#64 : BitVec 64) = 0 by rfl)] at hr
    apply receipt_status_branch_frame he p old 128 hp hw hfresh tail v hcont
    simpa only [evaluateHOLFiniteState_seq_line780] using hr
  · simp only [hz, ne_eq, not_false_eq_true, if_true, if_neg (show (1#64 : BitVec 64) ≠ 0 by decide)] at hr
    apply receipt_status_branch_frame he p old 1 hp hw hfresh tail v hcont
    simpa only [evaluateHOLFiniteState_seq_line780] using hr

end PtxP34

namespace PtxP34
open WkBlockTxEnc

/-- Status serialization advances the receipt cursor by exactly one byte and
retains all non-cursor, non-length locals for gas serialization. -/
theorem receipt_status_advance_continuation_frame {F : Type}
    {s mid post : PanSemStateFiniteExact 64 F} {R : List Ivl} {gw : List String}
    (he : HeapByteEff s mid R gw) (p old succeeded : BitVec 64)
    (hp : mid.locals.lookup (ofString "p") = some (.val (.word p)))
    (hw : mid.locals.lookup (ofString "w") = some (.val (.word old)))
    (hs : mid.locals.lookup (ofString "succeeded") = some (.val (.word succeeded)))
    (hfresh : globN s "heap_ptr" ≤ p.toNat ∧ p.toNat + 1 ≤ heapLimit)
    (tail : ProgHOL 64) (v : ValueHOL 64)
    (hcont : ∀ (next : PanSemStateFiniteExact 64 F) (q : BitVec 64),
      HeapByteEff s next R gw → q.toNat = p.toNat + 1 →
      next.locals.lookup (ofString "p") = some (.val (.word q)) →
      next.locals.lookup (ofString "w") = some (.val (.word 1#64)) →
      (∀ name, name ≠ ofString "p" → name ≠ ofString "w" →
        next.locals.lookup name = mid.locals.lookup name) →
      evaluateHOLFiniteState next tail = (some (.returned v), post) →
      HeapByteEff s post R gw)
    (hr : evaluateHOLFiniteState mid
      (.seq
        (.ite (.cmp .notEqual (.var .local (ofString "succeeded")) (.const 0))
          (.seq (.storeByte (.var .local (ofString "p")) (.const 1))
            (.assign .local (ofString "w") (.const 1)))
          (.seq (.storeByte (.var .local (ofString "p")) (.const 128))
            (.assign .local (ofString "w") (.const 1))))
        (.seq (.assign .local (ofString "p")
          (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])) tail)) =
      (some (.returned v), post)) : HeapByteEff s post R gw := by
  apply receipt_status_continuation_frame he p old succeeded hp hw hs hfresh _ v ?_ hr
  intro next he' hloc hr'
  have hp' : next.locals.lookup (ofString "p") = some (.val (.word p)) := by
    rw [hloc]
    simpa [HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "w" ≠ ofString "p" by decide] using hp
  have hw' : next.locals.lookup (ofString "w") = some (.val (.word 1#64)) := by
    rw [hloc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  apply receipt_cursor_continuation_frame he' p 1#64 hp' hw' tail v ?_ hr'
  intro final he'' hp'' hkeep hr''
  refine hcont final (p + 1#64) he'' ?_ hp'' ?_ ?_ hr''
  · rw [BitVec.toNat_add]
    change (p.toNat + 1) % 2 ^ 64 = p.toNat + 1
    apply Nat.mod_eq_of_lt
    have hlim : heapLimit < 2 ^ 64 := by decide
    omega
  · rw [hkeep _ (by decide)]; exact hw'
  · intro name hnp hnw
    rw [hkeep name hnp, hloc]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hnw]
end PtxP34

namespace PtxP34
open WkBlockTxEnc

/-- A word-local scope transports the heap frame through its returning body
and through restoration of the caller's local binding. -/
theorem receipt_dec_word_continuation_frame {F : Type}
    {s mid post : PanSemStateFiniteExact 64 F} {R : List Ivl} {gw : List String}
    (he : HeapByteEff s mid R gw) (name : MlS) (e : ExpHOL 64)
    (tail : ProgHOL 64) (v : ValueHOL 64)
    (hcont : ∀ (w : BitVec 64) (final : PanSemStateFiniteExact 64 F),
      evalAt mid e = some (.val (.word w)) →
      HeapByteEff s (setVarHOLFinite name (.val (.word w)) mid) R gw →
      evaluateHOLFiniteState (setVarHOLFinite name (.val (.word w)) mid) tail =
        (some (.returned v), final) → HeapByteEff s final R gw)
    (hr : evaluateHOLFiniteState mid (.dec name .one e tail) =
      (some (.returned v), post)) : HeapByteEff s post R gw := by
  rw [evaluateHOLFiniteState_dec_total] at hr
  dsimp only at hr
  split at hr
  · cases hr
  · rename_i value hev
    split at hr
    · rename_i hshape
      have hw : ∃ w : BitVec 64, value = .val (.word w) := by
        cases value with
        | val z => cases z with
          | word w => exact ⟨w, rfl⟩
        | _ => simp [shapeOfHOLExact, shapeEqHOL] at hshape
      obtain ⟨w, rfl⟩ := hw
      rcases hb : evaluateHOLFiniteState (setVarHOLFinite name (.val (.word w)) mid) tail with
        ⟨r, final⟩
      rw [hb] at hr
      have hf := hcont w final hev (he.locals_clock _ _)
        (by rw [← (Prod.mk.inj hr).1]; exact hb)
      have hp := (Prod.mk.inj hr).2.symm
      rw [hp]
      exact hf.locals_clock _ _
    · cases hr

end PtxP34

namespace PtxP34
open WkBlockTxEnc
open private WkBlockTxEnc.receiptKeccakIvls WkBlockTxEnc.logsEncodedSum
  from InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.EncodeReceipt

/-- Concrete receipt suffix starting with cumulative-gas serialization. -/
def receiptGasReturnCode : ProgHOL 64 :=
  .seq
    (.call (some (some (.local, ofString "w"), none)) (ofString "rlp_encode_word")
      [.var .local (ofString "p"), .var .local (ofString "cumulative_gas")])
    (.seq
      (.assign .local (ofString "p")
        (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
      (.decCall (ofString "bloom") .one (ofString "alloc") [.const 256]
        (.seq
          (.call (some (none, none)) (ofString "logs_bloom")
            [.var .local (ofString "logs"), .var .local (ofString "bloom")])
          (.seq
            (.call (some (some (.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
              [.var .local (ofString "p"), .var .local (ofString "bloom"), .const 256])
            (.seq
              (.assign .local (ofString "p")
                (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
              (.seq
                (.call (some (some (.local, ofString "w"), none)) (ofString "encode_logs")
                  [.var .local (ofString "p"), .var .local (ofString "logs")])
                (.seq
                  (.assign .local (ofString "p")
                    (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                  (.seq
                    (.call (some (some (.local, ofString "w"), none)) (ofString "rlp_finish_list")
                      [.var .local (ofString "start"), .var .local (ofString "p")])
                    (.seq
                      (.ite (.cmp .notEqual (.var .local (ofString "tx_type")) (.const 0))
                        (.seq
                          (.storeByte (.op .sub [.var .local (ofString "start"), .const 1])
                            (.var .local (ofString "tx_type")))
                          (.return (.rstruct
                            [.op .sub [.var .local (ofString "start"), .const 1],
                             .op .add [.var .local (ofString "w"), .const 1]]))) .skip)
                      (.return (.rstruct [.var .local (ofString "start"),
                        .var .local (ofString "w")])))))))))))

/-- The complete status-to-return suffix preserves the receipt entry frame. -/
theorem receipt_status_gas_return_frame {F : Type}
    {s mid post : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) (hma : s.memaddrs = ordinaryDomain)
    (he : HeapByteEff s mid (WkBlockTxEnc.receiptKeccakIvls s) ["heap_ptr"])
    (start p logs gas old succeeded : BitVec 64) (bound : Nat) (v : ValueHOL 64)
    (hs : mid.locals.lookup (ofString "start") = some (.val (.word start)))
    (hp : mid.locals.lookup (ofString "p") = some (.val (.word p)))
    (hl : mid.locals.lookup (ofString "logs") = some (.val (.word logs)))
    (hg : mid.locals.lookup (ofString "cumulative_gas") = some (.val (.word gas)))
    (hw : mid.locals.lookup (ofString "w") = some (.val (.word old)))
    (hsu : mid.locals.lookup (ofString "succeeded") = some (.val (.word succeeded)))
    (hle : start.toNat + 9 ≤ p.toNat)
    (hfresh : globN s "heap_ptr" + 1 ≤ start.toNat ∧ p.toNat + 275 + bound ≤ heapLimit)
    (hnz : logs.toNat ≠ 0) (hL : LogsListOK s logs.toNat) (hD : LogsDisjFixed s logs.toNat)
    (hfit : 9 + WkBlockTxEnc.logsEncodedSum s (memW s logs.toNat)
      (memW s (logs.toNat + 8)) ≤ bound)
    (hr : evaluateHOLFiniteState mid
      (.seq
        (.ite (.cmp .notEqual (.var .local (ofString "succeeded")) (.const 0))
          (.seq (.storeByte (.var .local (ofString "p")) (.const 1))
            (.assign .local (ofString "w") (.const 1)))
          (.seq (.storeByte (.var .local (ofString "p")) (.const 128))
            (.assign .local (ofString "w") (.const 1))))
        (.seq (.assign .local (ofString "p")
          (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
          receiptGasReturnCode)) = (some (.returned v), post)) :
    HeapByteEff s post (WkBlockTxEnc.receiptKeccakIvls s) ["heap_ptr"] := by
  apply receipt_status_advance_continuation_frame he p old succeeded hp hw hsu
    ⟨by omega, by omega⟩ _ v ?_ hr
  intro next q he' hq hp' hw' hkeep hr'
  apply receipt_gas_alloc_bloom_return_frame hA hma he' start q logs gas 1#64 bound v
  · rw [hkeep _ (by decide) (by decide)]; exact hs
  · exact hp'
  · rw [hkeep _ (by decide) (by decide)]; exact hl
  · rw [hkeep _ (by decide) (by decide)]; exact hg
  · exact hw'
  · omega
  · exact ⟨hfresh.1, by omega⟩
  · exact hnz
  · exact hL
  · exact hD
  · exact hfit
  · exact hr'

end PtxP34

namespace PtxP34
open WkBlockTxEnc
open private WkBlockTxEnc.receiptKeccakIvls WkBlockTxEnc.logsEncodedSum
  from InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.EncodeReceipt

/-- Concrete receipt suffix starting with the status byte. -/
def receiptStatusReturnCode : ProgHOL 64 :=
  .seq
    (.ite (.cmp .notEqual (.var .local (ofString "succeeded")) (.const 0))
      (.seq (.storeByte (.var .local (ofString "p")) (.const 1))
        (.assign .local (ofString "w") (.const 1)))
      (.seq (.storeByte (.var .local (ofString "p")) (.const 128))
        (.assign .local (ofString "w") (.const 1))))
    (.seq (.assign .local (ofString "p")
      (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
      receiptGasReturnCode)

/-- Initializing and restoring the scoped encoded-length local completes the
frame proof for the receipt's innermost declaration. -/
theorem receipt_length_scope_return_frame {F : Type}
    {s mid post : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) (hma : s.memaddrs = ordinaryDomain)
    (he : HeapByteEff s mid (WkBlockTxEnc.receiptKeccakIvls s) ["heap_ptr"])
    (start p logs gas succeeded : BitVec 64) (bound : Nat) (v : ValueHOL 64)
    (hs : mid.locals.lookup (ofString "start") = some (.val (.word start)))
    (hp : mid.locals.lookup (ofString "p") = some (.val (.word p)))
    (hl : mid.locals.lookup (ofString "logs") = some (.val (.word logs)))
    (hg : mid.locals.lookup (ofString "cumulative_gas") = some (.val (.word gas)))
    (hsu : mid.locals.lookup (ofString "succeeded") = some (.val (.word succeeded)))
    (hle : start.toNat + 9 ≤ p.toNat)
    (hfresh : globN s "heap_ptr" + 1 ≤ start.toNat ∧ p.toNat + 275 + bound ≤ heapLimit)
    (hnz : logs.toNat ≠ 0) (hL : LogsListOK s logs.toNat) (hD : LogsDisjFixed s logs.toNat)
    (hfit : 9 + WkBlockTxEnc.logsEncodedSum s (memW s logs.toNat)
      (memW s (logs.toNat + 8)) ≤ bound)
    (hr : evaluateHOLFiniteState mid
      (.dec (ofString "w") .one (.const 0) receiptStatusReturnCode) =
      (some (.returned v), post)) :
    HeapByteEff s post (WkBlockTxEnc.receiptKeccakIvls s) ["heap_ptr"] := by
  apply receipt_dec_word_continuation_frame he _ _ _ v ?_ hr
  intro w final _ he' hr'
  apply receipt_status_gas_return_frame hA hma he' start p logs gas w succeeded bound v
  · simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "w" ≠ ofString "start" by decide] using hs
  · simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "w" ≠ ofString "p" by decide] using hp
  · simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "w" ≠ ofString "logs" by decide] using hl
  · simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "w" ≠ ofString "cumulative_gas" by decide] using hg
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  · simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "w" ≠ ofString "succeeded" by decide] using hsu
  · exact hle
  · exact hfresh
  · exact hnz
  · exact hL
  · exact hD
  · exact hfit
  · exact hr'

end PtxP34

namespace PtxP34
open WkBlockTxEnc
open private WkBlockTxEnc.receiptKeccakIvls WkBlockTxEnc.logsEncodedSum
  from InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.EncodeReceipt

/-- Initializing the receipt cursor reserves the list header and frames the
entire remaining encoder, including restoration of both local scopes. -/
theorem receipt_cursor_scope_return_frame {F : Type}
    {s mid post : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) (hma : s.memaddrs = ordinaryDomain)
    (he : HeapByteEff s mid (WkBlockTxEnc.receiptKeccakIvls s) ["heap_ptr"])
    (start logs gas succeeded : BitVec 64) (bound : Nat) (v : ValueHOL 64)
    (hs : mid.locals.lookup (ofString "start") = some (.val (.word start)))
    (hl : mid.locals.lookup (ofString "logs") = some (.val (.word logs)))
    (hg : mid.locals.lookup (ofString "cumulative_gas") = some (.val (.word gas)))
    (hsu : mid.locals.lookup (ofString "succeeded") = some (.val (.word succeeded)))
    (hfresh : globN s "heap_ptr" + 1 ≤ start.toNat ∧ start.toNat + 284 + bound ≤ heapLimit)
    (hnz : logs.toNat ≠ 0) (hL : LogsListOK s logs.toNat) (hD : LogsDisjFixed s logs.toNat)
    (hfit : 9 + WkBlockTxEnc.logsEncodedSum s (memW s logs.toNat)
      (memW s (logs.toNat + 8)) ≤ bound)
    (hr : evaluateHOLFiniteState mid
      (.dec (ofString "p") .one (.op .add [.var .local (ofString "start"), .const 9])
        (.dec (ofString "w") .one (.const 0) receiptStatusReturnCode)) =
      (some (.returned v), post)) :
    HeapByteEff s post (WkBlockTxEnc.receiptKeccakIvls s) ["heap_ptr"] := by
  apply receipt_dec_word_continuation_frame he _ _ _ v ?_ hr
  intro p final hev he' hr'
  have hp : start + 9#64 = p := by
    simpa [evalAt, evalHOLExact, evalListHOLExact, hs, wordOpHOL, wordOp,
      valueIsWord, valueWord] using hev
  have hpn : p.toNat = start.toNat + 9 := by
    rw [← hp, BitVec.toNat_add]
    change (start.toNat + 9) % 2 ^ 64 = start.toNat + 9
    apply Nat.mod_eq_of_lt
    have hlim : heapLimit < 2 ^ 64 := by decide
    omega
  apply receipt_length_scope_return_frame hA hma he' start p logs gas succeeded bound v
  · simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "p" ≠ ofString "start" by decide] using hs
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  · simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "p" ≠ ofString "logs" by decide] using hl
  · simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "p" ≠ ofString "cumulative_gas" by decide] using hg
  · simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "p" ≠ ofString "succeeded" by decide] using hsu
  · omega
  · exact ⟨hfresh.1, by omega⟩
  · exact hnz
  · exact hL
  · exact hD
  · exact hfit
  · exact hr'

end PtxP34

namespace PtxP34
open WkBlockTxEnc
open private WkBlockTxEnc.receiptKeccakIvls WkBlockTxEnc.logsEncodedSum
  from InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.EncodeReceipt

/-- The receipt buffer's one-byte type-prefix reservation initializes all
three scoped locals and preserves the entry frame through return. -/
theorem receipt_start_scope_return_frame {F : Type}
    {s mid post : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) (hma : s.memaddrs = ordinaryDomain)
    (he : HeapByteEff s mid (WkBlockTxEnc.receiptKeccakIvls s) ["heap_ptr"])
    (buf logs gas succeeded : BitVec 64) (bound : Nat) (v : ValueHOL 64)
    (hb : mid.locals.lookup (ofString "buf") = some (.val (.word buf)))
    (hl : mid.locals.lookup (ofString "logs") = some (.val (.word logs)))
    (hg : mid.locals.lookup (ofString "cumulative_gas") = some (.val (.word gas)))
    (hsu : mid.locals.lookup (ofString "succeeded") = some (.val (.word succeeded)))
    (hfresh : globN s "heap_ptr" ≤ buf.toNat ∧ buf.toNat + 285 + bound ≤ heapLimit)
    (hnz : logs.toNat ≠ 0) (hL : LogsListOK s logs.toNat) (hD : LogsDisjFixed s logs.toNat)
    (hfit : 9 + WkBlockTxEnc.logsEncodedSum s (memW s logs.toNat)
      (memW s (logs.toNat + 8)) ≤ bound)
    (hr : evaluateHOLFiniteState mid
      (.dec (ofString "start") .one (.op .add [.var .local (ofString "buf"), .const 1])
        (.dec (ofString "p") .one (.op .add [.var .local (ofString "start"), .const 9])
          (.dec (ofString "w") .one (.const 0) receiptStatusReturnCode))) =
      (some (.returned v), post)) :
    HeapByteEff s post (WkBlockTxEnc.receiptKeccakIvls s) ["heap_ptr"] := by
  apply receipt_dec_word_continuation_frame he _ _ _ v ?_ hr
  intro start final hev he' hr'
  have hs : buf + 1#64 = start := by
    simpa [evalAt, evalHOLExact, evalListHOLExact, hb, wordOpHOL, wordOp,
      valueIsWord, valueWord] using hev
  have hsn : start.toNat = buf.toNat + 1 := by
    rw [← hs, BitVec.toNat_add]
    change (buf.toNat + 1) % 2 ^ 64 = buf.toNat + 1
    apply Nat.mod_eq_of_lt
    have hlim : heapLimit < 2 ^ 64 := by decide
    omega
  apply receipt_cursor_scope_return_frame hA hma he' start logs gas succeeded bound v
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  · simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "start" ≠ ofString "logs" by decide] using hl
  · simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "start" ≠ ofString "cumulative_gas" by decide] using hg
  · simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "start" ≠ ofString "succeeded" by decide] using hsu
  · constructor <;> omega
  · exact hnz
  · exact hL
  · exact hD
  · exact hfit
  · exact hr'

end PtxP34

namespace PtxP34
open WkBlockTxEnc
open private WkBlockTxEnc.receiptKeccakIvls WkBlockTxEnc.logsEncodedSum
  from InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.EncodeReceipt

/-- Receipt buffer allocation supplies enough fresh space to the complete
initialized encoder and restores the buffer local on return. -/
theorem receipt_buffer_alloc_return_frame {F : Type}
    {s mid post : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) (hma : s.memaddrs = ordinaryDomain)
    (he : HeapByteEff s mid (WkBlockTxEnc.receiptKeccakIvls s) ["heap_ptr"])
    (bound logs gas succeeded : BitVec 64) (v : ValueHOL 64)
    (hb : mid.locals.lookup (ofString "bound") = some (.val (.word bound)))
    (hl : mid.locals.lookup (ofString "logs") = some (.val (.word logs)))
    (hg : mid.locals.lookup (ofString "cumulative_gas") = some (.val (.word gas)))
    (hsu : mid.locals.lookup (ofString "succeeded") = some (.val (.word succeeded)))
    (hbound : bound.toNat + 400 < 2 ^ 64)
    (hnz : logs.toNat ≠ 0) (hL : LogsListOK s logs.toNat) (hD : LogsDisjFixed s logs.toNat)
    (hfit : 9 + WkBlockTxEnc.logsEncodedSum s (memW s logs.toNat)
      (memW s (logs.toNat + 8)) ≤ bound.toNat)
    (hr : evaluateHOLFiniteState mid
      (.decCall (ofString "buf") .one (ofString "alloc")
        [.op .add [.var .local (ofString "bound"), .const 400]]
        (.dec (ofString "start") .one (.op .add [.var .local (ofString "buf"), .const 1])
          (.dec (ofString "p") .one (.op .add [.var .local (ofString "start"), .const 9])
            (.dec (ofString "w") .one (.const 0) receiptStatusReturnCode)))) =
      (some (.returned v), post)) :
    HeapByteEff s post (WkBlockTxEnc.receiptKeccakIvls s) ["heap_ptr"] := by
  obtain ⟨buf, n, q, next, hn, hbuf, _, _, hspace, hlim, _, _, _, _, hloc,
      he', _, _, hrun⟩ := eval_decCall_alloc_resumes mid "buf"
        (.op .add [.var .local (ofString "bound"), .const 400]) _
        (WkBlockTxEnc.receiptKeccakIvls s) ["heap_ptr"] he.arena.1.code he.arena
        (by simp) (by rw [hr]; simp) (by rw [hr]; exact Or.inl ⟨v, rfl⟩)
  have hn' : n = bound + 400#64 := by
    simpa [evalHOLExact, evalListHOLExact, hb, wordOpHOL, wordOp,
      valueIsWord, valueWord] using hn.symm
  have hnn : n.toNat = bound.toNat + 400 := by
    rw [hn', BitVec.toNat_add]
    exact Nat.mod_eq_of_lt hbound
  have hret := congrArg Prod.fst (hrun.symm.trans hr)
  have hf : HeapByteEff s (evaluateHOLFiniteState next
      (.dec (ofString "start") .one (.op .add [.var .local (ofString "buf"), .const 1])
        (.dec (ofString "p") .one (.op .add [.var .local (ofString "start"), .const 9])
          (.dec (ofString "w") .one (.const 0) receiptStatusReturnCode)))).2
      (WkBlockTxEnc.receiptKeccakIvls s) ["heap_ptr"] := by
    apply receipt_start_scope_return_frame hA hma (he.trans he') buf logs gas succeeded bound.toNat v
    · rw [hloc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    · rw [hloc]; simpa [HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "buf" ≠ ofString "logs" by decide] using hl
    · rw [hloc]; simpa [HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "buf" ≠ ofString "cumulative_gas" by decide] using hg
    · rw [hloc]; simpa [HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "buf" ≠ ofString "succeeded" by decide] using hsu
    · constructor
      · rw [hbuf]; exact he.hp_le
      · rw [hnn] at hspace; omega
    · exact hnz
    · exact hL
    · exact hD
    · exact hfit
    · exact Prod.ext hret rfl
  rw [hr] at hrun
  have hp := congrArg Prod.snd hrun
  dsimp only at hp
  rw [hp]
  exact hf.locals_clock _ _

end PtxP34

namespace PtxP34
open WkBlockTxEnc
open private WkBlockTxEnc.receiptKeccakIvls WkBlockTxEnc.logsEncodedSum
  WkBlockTxEnc.eval_decCall_logs_encoded_bound
  from InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.EncodeReceipt

/-- The complete concrete receipt body preserves its entry heap frame. -/
theorem encode_receipt_body_heapByteEff {F : Type}
    (s post : PanSemStateFiniteExact 64 F)
    (logs gas succeeded : BitVec 64) (v : ValueHOL 64)
    (hAR : ArenaReady s)
    (hl : s.locals.lookup (ofString "logs") = some (.val (.word logs)))
    (hg : s.locals.lookup (ofString "cumulative_gas") = some (.val (.word gas)))
    (hsu : s.locals.lookup (ofString "succeeded") = some (.val (.word succeeded)))
    (hL : LogsListOK s logs.toNat) (hD : LogsDisjFixed s logs.toNat)
    (hr : evaluateHOLFiniteState s (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_encode_receipt) =
      (some (.returned v), post)) :
    HeapByteEff s post (WkBlockTxEnc.receiptKeccakIvls s) ["heap_ptr"] := by
  change evaluateHOLFiniteState s
    (.decCall (ofString "bound") .one (ofString "logs_encoded_bound")
      [.var .local (ofString "logs")]
      (.decCall (ofString "buf") .one (ofString "alloc")
        [.op .add [.var .local (ofString "bound"), .const 400]]
        (.dec (ofString "start") .one (.op .add [.var .local (ofString "buf"), .const 1])
          (.dec (ofString "p") .one (.op .add [.var .local (ofString "start"), .const 9])
            (.dec (ofString "w") .one (.const 0) receiptStatusReturnCode))))) =
      (some (.returned v), post) at hr
  obtain ⟨hnz, bound, mid, hbound, hsize, _, _, hloc, he, _, _, hrun⟩ :=
    WkBlockTxEnc.eval_decCall_logs_encoded_bound s logs _
      (WkBlockTxEnc.receiptKeccakIvls s) ["heap_ptr"] hAR.1.code hAR hl hL hD
      (by rw [hr]; simp) (by rw [hr]; exact Or.inl ⟨v, rfl⟩)
  have hret := congrArg Prod.fst (hrun.symm.trans hr)
  have hf : HeapByteEff s (evaluateHOLFiniteState mid
      (.decCall (ofString "buf") .one (ofString "alloc")
        [.op .add [.var .local (ofString "bound"), .const 400]]
        (.dec (ofString "start") .one (.op .add [.var .local (ofString "buf"), .const 1])
          (.dec (ofString "p") .one (.op .add [.var .local (ofString "start"), .const 9])
            (.dec (ofString "w") .one (.const 0) receiptStatusReturnCode))))).2
      (WkBlockTxEnc.receiptKeccakIvls s) ["heap_ptr"] := by
    apply receipt_buffer_alloc_return_frame hAR.2 hAR.1.memaddrs he bound logs gas succeeded v
    · rw [hloc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    · rw [hloc]; simpa [HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "bound" ≠ ofString "logs" by decide] using hl
    · rw [hloc]; simpa [HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "bound" ≠ ofString "cumulative_gas" by decide] using hg
    · rw [hloc]; simpa [HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "bound" ≠ ofString "succeeded" by decide] using hsu
    · omega
    · exact hnz
    · exact hL
    · exact hD
    · omega
    · exact Prod.ext hret rfl
  rw [hr] at hrun
  have hp := congrArg Prod.snd hrun
  dsimp only at hp
  rw [hp]
  exact hf.locals_clock _ _

end PtxP34

namespace PtxP34
open WkBlockTxEnc
open private WkBlockTxEnc.lookupCode_four_words WkBlockTxEnc.receiptKeccakIvls
  from InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.EncodeReceipt

/-- The concrete receipt call preserves both block-output backing pointers. -/
theorem encode_receipt_backing (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : Phase4ReceiptReady s) (hb : TxBacking s)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "encode_receipt") vs =
      some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post))
    (hg : locN (callEntryStateHOLFinite s callee) "logs" = locN s "logs") :
    TxBacking post := by
  have hl' := hl
  rw [hc] at hl'
  have hbr : body = GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_encode_receipt ∧
      ret = .comb [.one, .one] := by
    have hx := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup
      (ofString "encode_receipt") vs body callee ret hl'
    simp only [lookupCodeHOLExact, WkBlockTxEnc.lookup_encode_receipt] at hx
    split at hx <;> simp_all
  have hbody := hbr.1
  have hl'' := hl'
  rw [hbr.1, hbr.2] at hl''
  obtain ⟨tx, succeeded, gas, logs, _, _, hsu, hgas, hlogs⟩ :=
    WkBlockTxEnc.lookupCode_four_words (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) WkBlockTxEnc.lookup_encode_receipt hl''
  have hlogN : locN (callEntryStateHOLFinite s callee) "logs" = logs.toNat := by
    simp [locN, callEntryStateHOLFinite, hlogs]
  have hL : LogsListOK (callEntryStateHOLFinite s callee) logs.toNat := by
    rw [← hlogN, hg]
    exact (R13Shards.logsListOK_with_locals s callee (s.clock - 1) _).mpr hp.2.1
  have hD : LogsDisjFixed (callEntryStateHOLFinite s callee) logs.toNat := by
    rw [← hlogN, hg]; exact hp.2.2.1
  have he := encode_receipt_body_heapByteEff (callEntryStateHOLFinite s callee) post
    logs gas succeeded v (PtxP1.worldOK_callEntry hp.1.1.1 callee).1 hlogs hgas hsu hL hD
    (by rw [← hbody]; exact hr)
  apply encode_receipt_backing_of_heapByteEff h s vs body callee ret v post hc hp hb hl hr hg
  change WkBlockTxEnc.HeapByteEff (callEntryStateHOLFinite s callee) post
    (WkBlockTxEnc.receiptKeccakIvls (callEntryStateHOLFinite s callee)) ["heap_ptr"]
  exact he

end PtxP34

namespace PtxP34

/-- Receipt encoding and the remaining stable-copy prefix are now concrete;
only the credit call's strengthened preservation contract remains. -/
theorem phase4BackingPrefix_of_credit (h : PtxCallees)
    (hcredit : ∀ args : List (ExpHOL 64), Hoare TxAfterCallBackingStrong
      (.call (some (none, none)) (ofString "create_ether") args)
      (fun r t => r = none → TxAfterCallBackingStrong t)) :
    Phase4BackingPrefix :=
  phase4BackingPrefix_of_credit_encode h hcredit (encode_receipt_backing h)

end PtxP34

namespace PtxP34

/-- Keeping the two nested list backing words suffices for the credit calls. -/
theorem hoare_create_ether_backing_of_header_words
    (hdata : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) vs body callee ret v post,
      s.code = originalRuntimeCode → TxAfterCallBackingStrong s →
      lookupCodeHOLFinite s.code.lookup (ofString "create_ether") vs = some (body, callee, ret) →
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
        (some (.returned v), post) →
      ∀ k ∈ ([40, 72] : List Nat),
        memW post (memW s (globN s "bo" + k)) = memW s (memW s (globN s "bo" + k)))
    (args : List (ExpHOL 64)) :
    Hoare TxAfterCallBackingStrong
      (.call (some (none, none)) (ofString "create_ether") args)
      (fun r t => r = none → TxAfterCallBackingStrong t) := by
  apply R13Shards.Hoare.call0_resume
  intro F s vs body callee ret v post hc hp _ hl hr
  exact create_ether_backing_resume_of_header_words s vs body callee ret v post hc hl hr hp
    (hdata s vs body callee ret v post hc hp hl hr)

end PtxP34

namespace PtxP34
open private EvmEkFk.acct_copy_step
  from InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.AccountWk

/-- An allocation-only concrete effect frames every old aligned allocation,
including a nested block-output list header in scratch memory. -/
theorem worldEff_allocated_frame {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {gw : List String} (b : Ivl)
    (hA : ArenaOK s) (he : WorldEff s post [] [] gw)
    (hb : Allocated s b) (hb1 : b.1 % 8 = 0) (hb2 : b.2 % 8 = 0) :
    Allocated post b ∧ IvlUnhit s post b := by
  have hfr : FrameOutside s post ([] ++ [] ++ [freeGap s]) (heapFree s) := by
    intro a hk hf
    by_contra hn
    rcases he.cell_frame a hn with ⟨i, hi, _⟩ | ⟨g, hg, _⟩ | hgap | hheap
    · cases hi
    · cases hg
    · exact hk _ (by simp) hgap.2
    · exact hf hheap.2
  have hs := allocated_ivl_survives_step (old := []) (new := []) (R := [])
    hA he.arena.2 ⟨he.hp_lo, he.sp_hi⟩
    (by simp) (by simp) (by intro o ho; cases ho) hfr hb1 hb2 hb
    (by simp) (by simp)
  exact ⟨hs.1, hs.2.2⟩

/-- The concrete account-copy call in `create_ether` preserves old headers. -/
theorem acct_copy_allocated_frame {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (b : Ivl)
    (hc : s.code = originalRuntimeCode) (hA : ArenaReady s)
    (hb : Allocated s b) (hb1 : b.1 % 8 = 0) (hb2 : b.2 % 8 = 0)
    (hr : evaluateHOLFiniteState s
      (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy")
        [.var .local (ofString "a")]) = (none, post)) :
    Allocated post b ∧ IvlUnhit s post b := by
  have he := EvmEkFk.acct_copy_step s hc hA (by rw [hr]; simp)
    (by rw [hr]; exact Or.inl rfl)
  rw [hr] at he
  dsimp only at he
  exact worldEff_allocated_frame b hA.2 he.1 hb hb1 hb2

end PtxP34

namespace PtxP34

/-- Updating a freshly copied account cannot write an older list header.
The accumulated effect also allows intervening read-only arithmetic calls. -/
theorem fresh_account_balance_store_effect {F : Type}
    {s cur : PanSemStateFiniteExact 64 F}
    (bw : BitVec 64) (value : ValueHOL 64)
    (he : WorldEff s cur [] [] ["heap_ptr"])
    (ha : cur.locals.lookup (ofString "a") = some (.val (.word bw)))
    (hv : cur.locals.lookup (ofString "nb") = some value)
    (hlo : globN s "heap_ptr" ≤ bw.toNat) (hhi : bw.toNat + 56 ≤ heapLimit)
    (hflat : (flattenHOL value).length = 4) :
    WorldEff s (evaluateHOLFiniteState cur
      (.store (.op .add [.var .local (ofString "a"), .const 8])
        (.var .local (ofString "nb")))).2 [] [] ["heap_ptr"] := by
  apply EvmEkFk.worldEff_store_multi he _ _ 4 (by decide)
  · intro v hev
    simp [evalHOLExact, hv] at hev
    subst v
    exact hflat
  · intro x hx
    simp [evalHOLExact, evalListHOLExact, ha, wordOpHOL, wordOp,
      valueIsWord, valueWord] at hx
    subst x
    have hlim : heapLimit < 2 ^ 64 := by decide
    have hheap : heapLimit ≤ heapEnd := by decide
    have hx8 : (bw + 8#64).toNat = bw.toNat + 8 := by
      apply BitVec.toNat_add_of_lt
      change bw.toNat + 8 < 2 ^ 64
      omega
    rw [hx8]
    exact ⟨by omega, Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))⟩

/-- The balance store in `create_ether` frames every old aligned allocation. -/
theorem fresh_account_balance_store_frame {F : Type}
    {s cur post : PanSemStateFiniteExact 64 F} (b : Ivl)
    (bw : BitVec 64) (value : ValueHOL 64)
    (hA : ArenaOK s) (he : WorldEff s cur [] [] ["heap_ptr"])
    (ha : cur.locals.lookup (ofString "a") = some (.val (.word bw)))
    (hv : cur.locals.lookup (ofString "nb") = some value)
    (hlo : globN s "heap_ptr" ≤ bw.toNat) (hhi : bw.toNat + 56 ≤ heapLimit)
    (hflat : (flattenHOL value).length = 4)
    (hb : Allocated s b) (hb1 : b.1 % 8 = 0) (hb2 : b.2 % 8 = 0)
    (hr : evaluateHOLFiniteState cur
      (.store (.op .add [.var .local (ofString "a"), .const 8])
        (.var .local (ofString "nb"))) = (none, post)) :
    Allocated post b ∧ IvlUnhit s post b := by
  have hm := fresh_account_balance_store_effect bw value he ha hv hlo hhi hflat
  rw [hr] at hm
  exact worldEff_allocated_frame b hA hm hb hb1 hb2

end PtxP34

namespace PtxP34
open InitECandidate.Solver.GuestTrapAndLookup

/-- A concrete effect preserves old aligned allocations separated from its
explicit writes, including scratch-resident list headers. -/
theorem worldEff_separated_allocated_frame {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {R : List Ivl}
    {B : List (String × Nat)} {gw : List String} (b : Ivl)
    (hA : ArenaOK s) (he : WorldEff s post R B gw)
    (hb : Allocated s b) (hb1 : b.1 % 8 = 0) (hb2 : b.2 % 8 = 0)
    (hR : ∀ j ∈ R, Disj b j)
    (hB : ∀ g ∈ B, Disj b (bufferRegion s g)) :
    Allocated post b ∧ IvlUnhit s post b := by
  refine ⟨(show AllocatorGrows s post from ⟨he.hp_lo, he.sp_hi⟩).allocated hb, ?_⟩
  intro a ha8 hhit
  have hai : b.1 ≤ a.toNat ∧ a.toNat + 8 ≤ b.1 + b.2 := by
    unfold CellHits at hhit
    omega
  by_contra hn
  rcases he.cell_frame a hn with ⟨j, hj, hpos, hhit⟩ | ⟨g, hg, hpos, hhit⟩ | hgap | hheap
  · have hd := hR j hj
    unfold Disj at hd
    unfold CellHits at hhit
    rcases hd with hd | hd | hd | hd <;> omega
  · have hd := hB g hg
    unfold Disj at hd
    unfold CellHits at hhit
    rcases hd with hd | hd | hd | hd <;> omega
  · rcases hb with hb | hb
    · have hh := hA.2.2.1
      have hp := hA.2.1
      have hsep : heapLimit ≤ scratchStart := by decide
      unfold Inside at hb
      change 0 < (freeGap s).2 ∧ CellHits a.toNat (freeGap s) at hgap
      unfold CellHits freeGap at hgap
      dsimp only at hgap
      omega
    · unfold Inside at hb
      change 0 < (freeGap s).2 ∧ CellHits a.toNat (freeGap s) at hgap
      unfold CellHits freeGap at hgap
      dsimp only at hgap
      omega
  · rcases hb with hb | hb
    · unfold Inside at hb
      change 0 < (heapFree s).2 ∧ CellHits a.toNat (heapFree s) at hheap
      unfold CellHits heapFree at hheap
      dsimp only at hheap
      omega
    · have hs := hA.2.2.2.1
      have hf := hA.2.2.1
      have hp := hA.2.1
      have hsep : heapLimit ≤ scratchStart := by decide
      unfold Inside at hb
      change 0 < (heapFree s).2 ∧ CellHits a.toNat (heapFree s) at hheap
      unfold CellHits heapFree at hheap
      dsimp only at hheap
      omega

open InitECandidate.Solver.Wave8GuestInv.Fast_C08WkShard03

/-- The trie/decode path of account lookup frames existing separated headers. -/
theorem ws_get_account_optional_allocated_frame {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (b : Ivl) (v : ValueHOL 64)
    (hA : ArenaReady s)
    (hb : Allocated s b) (hb1 : b.1 % 8 = 0) (hb2 : b.2 % 8 = 0)
    (hB : ∀ g ∈ wsBufs, Disj b (bufferRegion s g))
    (hr : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_ws_get_account_optional) =
      (some (.returned v), post)) :
    Allocated post b ∧ IvlUnhit s post b := by
  have he := worldEff_ws_get_account_optional s s hA.2
    (WorldEff.refl s [] wsBufs wsGw hA hA.1.code)
    (by rw [hr]; simp) (by rw [hr]; exact Or.inl ⟨v, rfl⟩)
  rw [hr] at he
  exact worldEff_separated_allocated_frame b hA.2 he hb hb1 hb2
    (by intro j hj; cases hj) hB

/-- A typed table mutation frames every nonempty fixed object, including the
two block-output list headers. -/
theorem htab_mutation_fixed_frame {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {t : Nat} {b : Ivl}
    (hA : ArenaOK s) (hAp : ArenaOK post) (hT : WorldTypedWith s S Nd)
    (ht : t ∈ S) (hb : b ∈ fixedObjects s) (hbpos : b.2 ≠ 0)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hfr : FrameOutside s post (htabFootprint s t)
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr")) :
    IvlUnhit s post b := by
  have halloc := ((hT.2.2.1.1 b hb).resolve_left hbpos).1
  apply R10Shards.P26_P28.ivlUnhit_of_frameOutside_aligned hbpos hfr
  · intro j hj
    have hw := ((hT.1.2.1 t ht).1.1 j hj).2
    exact ⟨hw.1, hw.2.1⟩
  · have hs := hA.2.2.2.2.2.1
    have hp := hAp.2.2.2.2.2.1
    exact ⟨hs, by omega⟩
  · intro j hj
    exact (((hT.1.2.1 t ht).2 j hj).2 b hb).flip
  · exact InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs.disj_fresh_of_zero_or_allocated
      hA hAp hhp (Or.inr halloc)

end PtxP34

namespace PtxP34

/-- The concrete table-set contract preserves nonempty fixed objects. -/
theorem htab_set_fixed_frame {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64))
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (ret : ShapeHOL) (v : ValueHOL 64) (S Nd : List Nat) (b : Ivl)
    (hA : ArenaReady s) (hT : WorldTypedWith s S Nd)
    (ht : locN (callEntryStateHOLFinite s callee) "t" ∈ S)
    (hb : b ∈ fixedObjects s) (hbpos : b.2 ≠ 0)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "htab_set") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) : IvlUnhit s post b := by
  have ha : HtabArgWF (callEntryStateHOLFinite s callee) := by
    refine ⟨(arenaReady_with_locals s callee (s.clock - 1)).2 hA, ?_, ?_⟩
    · exact (htabWF_with_locals s callee (s.clock - 1) _).2 (hT.1.2.1 _ ht).1
    · exact fun i hi => ((hT.1.2.1 _ ht).2 i hi).1
  have hx := PtxP1.funSpec_at_lookup htab_set_spec s hA.1.code vs body callee ret hl ha
    (by rw [hr]; simp)
  rw [hr] at hx
  obtain ⟨hAp, _, _, _, hhp, _, hframe, _⟩ := hx v rfl
  exact htab_mutation_fixed_frame hA.2 hAp.2 hT ht hb hbpos hhp hframe

end PtxP34

namespace PtxP34

theorem txWorld_header_fixed {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hW : TxWorld s) (k : Nat) (hk : k ∈ ([40, 72] : List Nat)) :
    (memW s (globN s "bo" + k), 24) ∈ fixedObjects s := by
  have hE := hW.2
  have hk' : k = 40 ∨ k = 72 := by simpa using hk
  unfold fixedObjects
  apply List.mem_append_left
  apply List.mem_append_right
  rcases hk' with rfl | rfl <;>
    simp [blockOutObjects, hE.bo_nz, hE.bo40, hE.bo72]

/-- Table updates used by account lookup preserve both nested backing words. -/
theorem htab_set_tx_header_words {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64))
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (ret : ShapeHOL) (v : ValueHOL 64) (S Nd : List Nat)
    (hW : TxWorld s) (hT : WorldTypedWith s S Nd)
    (ht : locN (callEntryStateHOLFinite s callee) "t" ∈ S)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "htab_set") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    ∀ k ∈ ([40, 72] : List Nat),
      memW post (memW s (globN s "bo" + k)) = memW s (memW s (globN s "bo" + k)) := by
  intro k hk
  have hb := txWorld_header_fixed hW k hk
  have hf := (hT.2.2.1.1 _ hb).resolve_left (by simp)
  have hu := htab_set_fixed_frame s post vs body callee ret v S Nd _ hW.1.1 hT ht hb
    (by simp) hl hr
  apply memW_eq_of_ivlUnhit hu hf.2.1 (ivl_allocated_bound hW.1.1.2 hf.1).2
  exact ⟨le_rfl, by dsimp; omega⟩

end PtxP34

namespace PtxP34
open InitECandidate.Solver.GuestTrapAndLookup
open private EvmEkFk.acct_new_params
  from InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.WkGetAccount

/-- Account construction only writes fresh storage and preserves old headers. -/
theorem acct_new_allocated_frame {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64))
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (ret : ShapeHOL) (v : ValueHOL 64) (b : Ivl)
    (hA : ArenaReady s)
    (hb : Allocated s b) (hb1 : b.1 % 8 = 0) (hb2 : b.2 % 8 = 0)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "acct_new") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) : Allocated post b ∧ IvlUnhit s post b := by
  have hbdy := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup (ofString "acct_new")
    _ _ body _ ret vs callee EvmEkFk.lookup_acct_new (by rwa [← hA.1.code])
  have hret := lookupCodeHOLFinite_installed_return s (ofString "acct_new")
    _ _ _ _ ret vs callee (by rw [hA.1.code]; exact EvmEkFk.lookup_acct_new) hl
  subst body ret
  have hl' := hl
  rw [hA.1.code] at hl'
  obtain ⟨wn, wc, vb, hsh, hn, hbal, hc⟩ := EvmEkFk.acct_new_params hl'
  have he := EvmEkFk.worldEff_acct_new s (callEntryStateHOLFinite s callee)
    (Rl := []) (B := []) (gw := ["heap_ptr"]) (by decide)
    ((WorldEff.refl s [] [] ["heap_ptr"] hA hA.1.code).locals_clock callee (s.clock - 1))
    hsh hn hbal hc (by rw [hr]; simp) (by rw [hr]; exact Or.inl ⟨v, rfl⟩)
  rw [hr] at he
  exact worldEff_allocated_frame b hA.2 he hb hb1 hb2

/-- The missing-account branch of lookup has an allocation-only effect. -/
theorem acct_empty_body_effect {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hA : ArenaReady s)
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_acct_empty)).1 ≠ some .timeOut)
    (hr : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_acct_empty)).1) :
    WorldEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_acct_empty)).2
      [] [] ["heap_ptr"] := by
  have he := WorldEff.refl s [] [] ["heap_ptr"] hA hA.1.code
  change WorldEff s (evaluateHOLFiniteState s
    (.decCall (ofString "a") .one (ofString "acct_new")
      [.const 0, .rstruct [.const 0, .const 0, .const 0, .const 0],
        .var .global (ofString "empty_code_hash")]
      (.return (.var .local (ofString "a"))))).2 [] [] ["heap_ptr"]
  apply worldEff_decCall_eff he (ofString "a") .one (ofString "acct_new") _ _ _ _
    EvmEkFk.lookup_acct_new
  · intro callee vals _ hl
    dsimp only
    intro hntc hrc
    have hl' := hl
    rw [hA.1.code] at hl'
    obtain ⟨wn, wc, vb, hsh, hn, hb, hc⟩ := EvmEkFk.acct_new_params hl'
    exact EvmEkFk.worldEff_acct_new s (callEntryStateHOLFinite s callee)
      (by decide) (he.locals_clock _ _) hsh hn hb hc hntc hrc
  · intro callee vals rv post _ _ _ _ hepost
    dsimp only
    intro _ _
    exact worldEff_return (hepost.locals_clock _ _) _
  · exact hnt
  · exact Or.inr (Or.inr (Or.inr hr))

end PtxP34

namespace PtxP34
open InitECandidate.Solver.GuestTrapAndLookup

/-- Returning from the missing-account constructor preserves old headers. -/
theorem acct_empty_allocated_frame {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64))
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (ret : ShapeHOL) (v : ValueHOL 64) (b : Ivl)
    (hA : ArenaReady s)
    (hb : Allocated s b) (hb1 : b.1 % 8 = 0) (hb2 : b.2 % 8 = 0)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "acct_empty") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) : Allocated post b ∧ IvlUnhit s post b := by
  have hbdy := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup (ofString "acct_empty")
    _ _ body _ ret vs callee EvmEkFk.lookup_acct_empty (by rwa [← hA.1.code])
  subst body
  change evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
    (sourceFnBody Guest.Software.guestFn_acct_empty) = (some (.returned v), post) at hr
  have he := acct_empty_body_effect (callEntryStateHOLFinite s callee)
    ((arenaReady_with_locals s callee (s.clock - 1)).2 hA)
    (by rw [hr]; simp) (by rw [hr]; exact Or.inl ⟨v, rfl⟩)
  rw [hr] at he
  exact worldEff_allocated_frame (s := callEntryStateHOLFinite s callee) b hA.2 he hb hb1 hb2

end PtxP34

namespace PtxP34
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs

/-- A concrete table-slot update preserves every nonempty fixed object. -/
theorem htab_set_recSlot_fixed_frame {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (S Nd : List Nat) (b : Ivl)
    (recName : String) (off : BitVec 64) (key value : ExpHOL 64)
    (hA : ArenaReady s) (hT : WorldTypedWith s S Nd)
    (hb : b ∈ fixedObjects s) (hbpos : b.2 ≠ 0)
    (hoff : off.toNat < sourceBase)
    (ht : globN s recName ≠ 0 → memW s (globN s recName + off.toNat) ≠ 0 →
      memW s (globN s recName + off.toNat) ∈ S)
    (hr : evaluateHOLFiniteState s (.call (some (none, none)) (ofString "htab_set")
      [.load .one (.op .add [.var .global (ofString recName), .const off]), key, value]) =
      (none, post)) : IvlUnhit s post b := by
  classical
  rw [evaluateHOLFiniteState_call] at hr
  rcases ha : evalListHOLFinite s
      [.load .one (.op .add [.var .global (ofString recName), .const off]), key, value]
      with _ | values
  · rw [ha] at hr
    cases hr
  · simp only [ha] at hr
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "htab_set") values with _ | ⟨body, callee, ret⟩
    · simp [hl] at hr
    · simp only [hl] at hr
      split at hr
      · cases hr
      · obtain ⟨v1, _, _, he1, _, _, hc_t, _, _⟩ := R16WkAcctWs.callee_param_three s (ofString "htab_set")
          (ofString "t") (ofString "key") (ofString "value") .one .one .one _ _
          (by rw [hA.1.code]; exact EvmFrameSpecs.lookup_htab_set)
          _ _ _ values body callee ret ha hl
        obtain ⟨tw, rfl, htw, hnz⟩ := evalAt_loadG_nz s hA.1 recName off hoff v1 he1
        have hloc : locN (callEntryStateHOLFinite s callee) "t" =
            memW s (globN s recName + off.toNat) := by
          simp [locN, callEntryStateHOLFinite, hc_t, htw]
        rcases hc : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨r, p⟩
        rw [hc] at hr
        cases r with
        | none => cases hr
        | some r =>
          cases r <;> try (simp at hr)
          rename_i v
          split at hr
          · have hzn := PtxP1.funSpec_at_lookup EvmFrameSpecs.nz_htab_set
              s hA.1.code values body callee ret hl
              (guestInv_callEntry s callee hA.1) (by rw [hc]; simp)
            rw [hc] at hzn
            have hm : locN (callEntryStateHOLFinite s callee) "t" ∈ S := by
              rw [hloc]
              apply ht hnz
              rw [← hloc]
              exact hzn (Or.inl ⟨v, rfl⟩)
            have hu := htab_set_fixed_frame s p values body callee ret v S Nd b hA hT hm hb hbpos hl hc
            have hp := (Prod.mk.inj hr).2
            rw [← hp]
            exact hu
          · cases hr

end PtxP34

namespace PtxP34

/-- Recording a pre-state read preserves the fixed headers used by credit. -/
theorem record_pre_state_read_body_fixed_frame {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (S Nd : List Nat) (b : Ivl) (v : ValueHOL 64)
    (hA : ArenaReady s) (hT : WorldTypedWith s S Nd)
    (hb : b ∈ fixedObjects s) (hbpos : b.2 ≠ 0)
    (hr : evaluateHOLFiniteState s (InitECandidate.Solver.GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_record_pre_state_read) =
      (some (.returned v), post)) : IvlUnhit s post b := by
  change evaluateHOLFiniteState s (.seq (.call (some (none, none)) (ofString "htab_set")
    [.load .one (.op .add [.var .global (ofString "bs"), .const 72]),
     .var .local (ofString "addr"), .const 1]) (.return (.const 0))) = _ at hr
  obtain ⟨mid, hc, _, _, ht⟩ := ignored_call_seq_returned hr
  have hu := htab_set_recSlot_fixed_frame s mid S Nd b "bs" 72 _ _ hA hT hb hbpos
    (by decide) (fun hn hz => (hT.1.2.2.2.2.1 72 (by simp [bsTableSlots]) hn).resolve_left hz) hc
  rw [evaluateHOLFiniteState_return] at ht
  simp only [evalHOLExact] at ht
  split at ht
  · have hp := (Prod.mk.inj ht).2
    subst post
    exact hu
  · cases ht

end PtxP34

namespace PtxP34
open InitECandidate.Solver.GuestTrapAndLookup

/-- Lift the concrete pre-state read frame to its installed callee interface. -/
theorem record_pre_state_read_fixed_frame {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64))
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (ret : ShapeHOL) (v : ValueHOL 64) (S Nd : List Nat) (b : Ivl)
    (hA : ArenaReady s) (hT : WorldTypedWith s S Nd)
    (hb : b ∈ fixedObjects s) (hbpos : b.2 ≠ 0)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "record_pre_state_read") vs =
      some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) : IvlUnhit s post b := by
  have hbdy := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup
    (ofString "record_pre_state_read") _ _ body _ ret vs callee
    R16WkAcctWs.lookup_record_pre_state_read (by rwa [← hA.1.code])
  subst body
  change evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
    (sourceFnBody Guest.Software.guestFn_record_pre_state_read) = (some (.returned v), post) at hr
  exact record_pre_state_read_body_fixed_frame (callEntryStateHOLFinite s callee) post S Nd b v
    ((arenaReady_with_locals s callee (s.clock - 1)).2 hA)
    ((R13Shards.worldTypedWith_with_locals s callee (s.clock - 1) S Nd).2 hT) hb hbpos hr

end PtxP34

namespace PtxP34

/-- Convert a fixed-object frame into the two backing-word equalities. -/
theorem tx_header_words_of_fixed_frame {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hW : TxWorld s) (hT : WorldTypedWith s S Nd)
    (hframe : ∀ b ∈ fixedObjects s, b.2 ≠ 0 → IvlUnhit s post b) :
    ∀ k ∈ ([40, 72] : List Nat),
      memW post (memW s (globN s "bo" + k)) = memW s (memW s (globN s "bo" + k)) := by
  intro k hk
  have hb := txWorld_header_fixed hW k hk
  have hf := (hT.2.2.1.1 _ hb).resolve_left (by simp)
  apply memW_eq_of_ivlUnhit (hframe _ hb (by simp)) hf.2.1
    (ivl_allocated_bound hW.1.1.2 hf.1).2
  exact ⟨le_rfl, by dsimp; omega⟩

end PtxP34

namespace PtxP34
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.Wave8GuestInv.Fast_C08WkShard03

/-- The installed trie/decode callee preserves separated old allocations. -/
theorem ws_get_account_optional_call_allocated_frame {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64))
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (ret : ShapeHOL) (v : ValueHOL 64) (b : Ivl)
    (hA : ArenaReady s)
    (hb : Allocated s b) (hb1 : b.1 % 8 = 0) (hb2 : b.2 % 8 = 0)
    (hB : ∀ g ∈ wsBufs, Disj b (bufferRegion s g))
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "ws_get_account_optional") vs =
      some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) : Allocated post b ∧ IvlUnhit s post b := by
  have hbdy := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup
    (ofString "ws_get_account_optional") _ _ body _ ret vs callee
    lookup_ws_get_account_optional_top (by rwa [← hA.1.code])
  subst body
  change evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
    (sourceFnBody Guest.Software.guestFn_ws_get_account_optional) = (some (.returned v), post) at hr
  exact ws_get_account_optional_allocated_frame (callEntryStateHOLFinite s callee) post b v
    ((arenaReady_with_locals s callee (s.clock - 1)).2 hA) hb hb1 hb2 hB hr

end PtxP34

namespace PtxP34

/-- Block-output objects are separated from the global scratch buffers. -/
theorem blockOut_disj_global_buffer {F : Type}
    {s : PanSemStateFiniteExact 64 F} {b : Ivl} {g : String × Nat}
    (hfix : FixedTyped s) (hb : b ∈ blockOutObjects s) (hg : g ∈ globalBuffers) :
    Disj b (bufferRegion s g) := by
  have hp := hfix.2
  unfold fixedObjects at hp
  have hpair := (List.pairwise_append.mp hp).1
  have hbg : bufferRegion s g ∈ globalBuffers.map
      (fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) := by
    exact List.mem_map.mpr ⟨g, hg, rfl⟩
  have hp3 := (List.pairwise_append.mp hpair).2.2
  have hd := hp3 (bufferRegion s g) (List.mem_append_left _ hbg) b hb
  simpa only [Disj, or_comm, or_left_comm, or_assoc] using hd

end PtxP34

namespace PtxP34
open InitECandidate.Solver.Wave8GuestInv.Fast_C08WkShard03

/-- Trie account lookup preserves both transaction backing-pointer words. -/
theorem ws_get_account_optional_tx_header_words {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64))
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (ret : ShapeHOL) (v : ValueHOL 64) (S Nd : List Nat)
    (hW : TxWorld s) (hT : WorldTypedWith s S Nd)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "ws_get_account_optional") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    ∀ k ∈ ([40, 72] : List Nat),
      memW post (memW s (globN s "bo" + k)) = memW s (memW s (globN s "bo" + k)) := by
  intro k hk
  have hb := txWorld_header_fixed hW k hk
  have hf := (hT.2.2.1.1 _ hb).resolve_left (by simp)
  have hbo : (memW s (globN s "bo" + k), 24) ∈ blockOutObjects s := by
    have hk' : k = 40 ∨ k = 72 := by simpa using hk
    rcases hk' with rfl | rfl <;> simp [blockOutObjects, hW.2.bo_nz, hW.2.bo40, hW.2.bo72]
  have hB : ∀ g ∈ wsBufs, Disj (memW s (globN s "bo" + k), 24) (bufferRegion s g) := by
    intro g hg
    apply blockOut_disj_global_buffer hT.2.2.1 hbo
    simp only [wsBufs, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl <;> decide
  have hu := ws_get_account_optional_call_allocated_frame s post vs body callee ret v _
    hW.1.1 hf.1 hf.2.1 (by simp) hB hl hr
  apply memW_eq_of_ivlUnhit hu.2 hf.2.1 (ivl_allocated_bound hW.1.1.2 hf.1).2
  exact ⟨le_rfl, by dsimp; omega⟩

end PtxP34

namespace PtxP34

/-- The missing-account allocation branch preserves transaction backing words. -/
theorem acct_empty_tx_header_words {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64))
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (ret : ShapeHOL) (v : ValueHOL 64) (S Nd : List Nat)
    (hW : TxWorld s) (hT : WorldTypedWith s S Nd)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "acct_empty") vs = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    ∀ k ∈ ([40, 72] : List Nat),
      memW post (memW s (globN s "bo" + k)) = memW s (memW s (globN s "bo" + k)) := by
  apply tx_header_words_of_fixed_frame hW hT
  intro b hb hn
  have hf := (hT.2.2.1.1 b hb).resolve_left hn
  exact (acct_empty_allocated_frame s post vs body callee ret v b hW.1.1
    hf.1 hf.2.1 hf.2.2.1 hl hr).2

end PtxP34

namespace PtxP34

/-- Compose backing-word preservation across a step retaining the header roots. -/
theorem tx_header_words_trans {F : Type}
    {s mid post : PanSemStateFiniteExact 64 F}
    (hbo : globN mid "bo" = globN s "bo")
    (hheaders : ∀ k ∈ ([40, 72] : List Nat),
      memW mid (globN s "bo" + k) = memW s (globN s "bo" + k))
    (hfirst : ∀ k ∈ ([40, 72] : List Nat),
      memW mid (memW s (globN s "bo" + k)) = memW s (memW s (globN s "bo" + k)))
    (hsecond : ∀ k ∈ ([40, 72] : List Nat),
      memW post (memW mid (globN mid "bo" + k)) = memW mid (memW mid (globN mid "bo" + k))) :
    ∀ k ∈ ([40, 72] : List Nat),
      memW post (memW s (globN s "bo" + k)) = memW s (memW s (globN s "bo" + k)) := by
  intro k hk
  have h := hsecond k hk
  rw [hbo, hheaders k hk] at h
  exact h.trans (hfirst k hk)

end PtxP34

namespace PtxP34

/-- Extract stable header roots from a world step without scratch writes. -/
theorem worldStep_empty_tx_header_roots {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {gw : List String}
    {keep : List (String × List Nat)} {boKeep : List Nat}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {r : Option (PanSemResultExact 64)}
    (hs : WorldStep (fun _ => []) gw keep Q s r post)
    (hW : TxWorld s) (hg : ofString "bo" ∉ gw.map ofString)
    (hk : ("bo", boKeep) ∈ keep)
    (hoff : ∀ k ∈ ([40, 72] : List Nat), k ∈ boKeep) :
    globN post "bo" = globN s "bo" ∧
      ∀ k ∈ ([40, 72] : List Nat), memW post (globN s "bo" + k) = memW s (globN s "bo" + k) := by
  refine ⟨R16Shards.globN_eq_of_lookup (hs.2.2.1 _ hg), ?_⟩
  intro k hmem
  exact hs.2.2.2.1 ("bo", boKeep) hk hW.2.bo_nz k (hoff k hmem)
    (by intro i hi; cases hi)

end PtxP34

end InitECandidate.Solver.Wave8GuestInv.R16Shards
