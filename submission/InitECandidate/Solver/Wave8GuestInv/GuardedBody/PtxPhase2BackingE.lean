import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase2BackingD2

/-!
# Phase 2 backing replay, region E (guest spine 53..69)

This file replays the te-suffix segment (the frozen
`phase2_teSuf_bound` of `PtxPhase2Strong`, guest spine 53..69) over the
region-D exit invariant `ptxPhase2CRInv` strengthened with the auxiliary
conjunct `PtxPhase2X`. Region E is pure preservation: the entry and exit
guards coincide (`ptxPhase2EInv`), the segment neither allocates
bookkeeping visible to Phase 4 nor disturbs the block-out record beyond
what the frozen proof already controls.

The CRInv part is the frozen `PtxTeSufInv` replay minus the sender
witness (dropped at the region-C cut): every witness position shifts one
conjunction to the left. The X part rides on Pre's toolkit: te-block
stores through `ptxPhase2_teStoreX_words`, the `alloc` call through
`M27.alloc_body_run` (memory and all globals but `heap_ptr` kept), and
the `keccak256` call through `Keccak256.call0_byteEff` with
`funByteEff_keccak256` (globals kept, writes confined to the two keccak
buffers and the fresh hash block).
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

/-! ## The region-E invariant -/

/-- Region E invariant: the region-D exit invariant (the te-suffix
invariant without the sender witness) paired with the auxiliary conjunct.
Entry and exit of region E coincide. -/
def ptxPhase2EInv {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  ptxPhase2CRInv s ∧ PtxPhase2X s

/-- State after the hash-buffer allocation: the region-E invariant, the
fresh buffer's word, alignment and separation, and the extended
ownership bundle (the al-addresses witness of the frozen
`PtxTeSufHashWitness`, without the sender copy). -/
def ptxPhase2EHashReady {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  ptxPhase2EInv s ∧
  (∃ w : BitVec 64, s.locals.lookup (ofString "txh") = some (.val (.word w)) ∧
    w.toNat % 8 = 0 ∧
    Disj (locN s "te", 200) (w.toNat, 32) ∧ Disj (locN s "tx", 384) (w.toNat, 32) ∧
    (0 < memW s (locN s "tx" + 216) →
      Disj (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216)) (w.toNat, 32)) ∧
    PtxTeSufHashWitness s (locN s "al_addrs", (locN s "nal" + 1) * 8) (locN s "txh"))

/-- The region-E invariant together with the fresh hash-buffer word. -/
def ptxPhase2ETxh {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  ptxPhase2EInv s ∧ ∃ w : BitVec 64, s.locals.lookup (ofString "txh") = some (.val (.word w))

/-! ## Locals- and clock-insensitivity -/

/-- Every auxiliary-conjunct name is a te-suffix name. -/
theorem ptxPhase2EXNames_sub {n : String} (hn : n ∈ ptxPhase2XNames) :
    n ∈ phase2_teSufNames := by
  simp only [ptxPhase2XNames, phase2_teSufNames, List.mem_cons, List.not_mem_nil, or_false] at hn ⊢
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- The region-C entry invariant only reads the listed caller locals. -/
theorem ptxPhase2CRInv_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (clock : Nat)
    (hl : ∀ name ∈ phase2_teSufNames,
      locals.lookup (ofString name) = s.locals.lookup (ofString name))
    (hp : ptxPhase2CRInv s) : ptxPhase2CRInv { s with locals := locals, clock := clock } := by
  have h11 : ∀ name ∈ (["te", "tx", "index", "sender", "mgas", "reservoir", "gas",
      "tx_blob_gas_used", "price", "enc", "intrinsic"] : List String),
      locals.lookup (ofString name) = s.locals.lookup (ofString name) :=
    fun name hn => hl name (phase2_teSufNames_eleven hn)
  have hte := locN_congr s locals clock "te" (hl "te" (by simp [phase2_teSufNames]))
  have htx := locN_congr s locals clock "tx" (hl "tx" (by simp [phase2_teSufNames]))
  have hnal := locN_congr s locals clock "nal" (hl "nal" (by simp [phase2_teSufNames]))
  have hala := locN_congr s locals clock "al_addrs" (hl "al_addrs" (by simp [phase2_teSufNames]))
  refine ⟨⟨phase2_teStoreReady_with_locals s locals clock h11 hp.1.1, ?_, ?_⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨w, hw⟩ := hp.1.2.1
    exact ⟨w, by rw [hl "nal" (by simp [phase2_teSufNames])]; exact hw⟩
  · rcases hp.1.2.2 with h | h
    · exact Or.inl (by rw [hnal]; exact h)
    · refine Or.inr ?_
      rw [hnal, htx]
      exact h
  · obtain ⟨w, hw⟩ := hp.2.1
    exact ⟨w, by rw [hl "nkeys" (by simp [phase2_teSufNames])]; exact hw⟩
  · obtain ⟨w, hw⟩ := hp.2.2.1
    exact ⟨w, by rw [hl "al_keys" (by simp [phase2_teSufNames])]; exact hw⟩
  · obtain ⟨w, hw⟩ := hp.2.2.2.1
    exact ⟨w, by rw [hl "al_addrs" (by simp [phase2_teSufNames])]; exact hw⟩
  · have hbuf := phase2_teSufWitness_with_locals s locals clock
      (locN s "al_addrs", (locN s "nal" + 1) * 8) htx hte hp.2.2.2.2.1
    rw [hala, hnal]
    exact hbuf
  · rw [hala, hnal]
    exact hp.2.2.2.2.2

/-- The region-E invariant only reads the listed caller locals. -/
theorem ptxPhase2EInv_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (clock : Nat)
    (hl : ∀ name ∈ phase2_teSufNames,
      locals.lookup (ofString name) = s.locals.lookup (ofString name))
    (hp : ptxPhase2EInv s) : ptxPhase2EInv { s with locals := locals, clock := clock } :=
  ⟨ptxPhase2CRInv_with_locals s locals clock hl hp.1,
    ptxPhase2X_with_locals s locals clock (fun n hn => hl n (ptxPhase2EXNames_sub hn)) hp.2⟩

/-- Assigning an unrelated local keeps the region-E invariant. -/
theorem ptxPhase2EInv_set_other {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : ptxPhase2EInv s) (name : MlS) (v : ValueHOL 64)
    (hne : ∀ n ∈ phase2_teSufNames, ofString n ≠ name) :
    ptxPhase2EInv (setVarHOLFinite name v s) :=
  ptxPhase2EInv_with_locals s _ s.clock
    (fun n hn => by simp [HolFiniteMapExact.update, FUPDATE, Ne.symm (hne n hn)]) hp

/-! ## Separation helpers for the fixed objects -/

/-- The keccak buffer regions as members of the `gbs` sublist. -/
private theorem ptxPhase2E_gbs_mem {F : Type} (s : PanSemStateFiniteExact 64 F)
    (gn : String × Nat) (hgn : gn ∈ globalBuffers) :
    (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2) ∈
      globalBuffers.map fun g => (globN s g.1, if globN s g.1 = 0 then 0 else g.2) :=
  List.mem_map.2 ⟨gn, hgn, rfl⟩

/-- The block-out record region `(bo, 88)` is a `gbs` member when `bo` is
nonzero. -/
private theorem ptxPhase2E_bo_gbs {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hbo : globN s "bo" ≠ 0) :
    (globN s "bo", 88) ∈
      globalBuffers.map fun g => (globN s g.1, if globN s g.1 = 0 then 0 else g.2) := by
  refine List.mem_map.2 ⟨("bo", 88), by simp [globalBuffers], ?_⟩
  simp [hbo]

/-- A keccak buffer region is disjoint from the block-out record region:
both are global buffers, and the fixed objects are pairwise disjoint. -/
theorem ptxPhase2E_disj_bo_keccakBuf {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hF : FixedTyped s) (hbo : globN s "bo" ≠ 0) {gn : String × Nat}
    (hgn : gn ∈ globalBuffers) (hne : gn.2 ≠ 88) :
    Disj (globN s "bo", 88) (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2) := by
  obtain ⟨hgbs, _, _, _, _⟩ := fixedObjects_disj_parts hF
  refine pairwise_disj_mem hgbs (ptxPhase2E_bo_gbs s hbo)
    (ptxPhase2E_gbs_mem s gn hgn) ?_
  intro heq
  have h2 : (88 : Nat) = if globN s gn.1 = 0 then 0 else gn.2 := congrArg Prod.snd heq
  by_cases hz : globN s gn.1 = 0
  · rw [if_pos hz] at h2; omega
  · rw [if_neg hz] at h2; exact hne h2.symm

/-! ## The te-suffix stores -/

/-- Program-level store rule for the region-E invariant: any word-valued
source stored inside the environment preserves the region-C entry
invariant. -/
theorem ptxPhase2CRInv_store_mem {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : ptxPhase2CRInv s) {x : BitVec 64} (hdom : s.memaddrs x)
    (hin : Inside (x.toNat, 8) (locN s "te") (locN s "te" + 200))
    {mem : BitVec 64 → HolWordLab 64} (hmem : ∀ a, a ≠ x → mem a = s.memory a) :
    ptxPhase2CRInv { s with memory := mem } := by
  obtain ⟨hl, S₀, Nd₀, hW₀, hT₀, hd₀, htx₀, hrec₀⟩ := hp.1.1
  have hps : PtxTeStoreReady s := hp.1.1
  have hsr : PtxTeStoreReady { s with memory := mem } :=
    phase2_teStoreReady_store hps hdom hin hmem
  have hu : IvlUnhit s { s with memory := mem } (locN s "tx", 384) :=
    ivlUnhit_single hmem (by simp) (disj_of_inside_right hin htx₀)
  have hA := hl.1.1.1.1.1.1
  have htwords := hT₀.1.1
  have hthi := (ivl_allocated_bound hA.2 (Or.inl hT₀.1.2.1)).2
  have hmemW216 : memW { s with memory := mem } (locN s "tx" + 216) =
      memW s (locN s "tx" + 216) :=
    memW_eq_of_ivlUnhit hu (by have := htwords.1; omega) hthi
      ⟨by dsimp; omega, by dsimp; omega⟩
  obtain ⟨S₁, Nd₁, hW₁, hT₁, hd₁, hte₁⟩ := hp.2.2.2.2.1
  refine ⟨⟨hsr, hp.1.2.1, ?_⟩, hp.2.1, hp.2.2.1, hp.2.2.2.1, ⟨S₁, Nd₁,
    phase2_teSufWitness_store hps hW₁ hT₁ hd₁ hte₁ hdom hin hmem⟩, hp.2.2.2.2.2⟩
  rcases hp.1.2.2 with h | h
  · exact Or.inl h
  · refine Or.inr ?_
    show locN s "nal" = memW { s with memory := mem } (locN s "tx" + 216)
    rw [hmemW216]
    exact h

/-- Generic te-store rule for the region-E invariant: the CRInv part via
the frozen suffix store rule, the X part via Pre's te-store toolkit. -/
theorem ptxPhase2E_offset_hoare (off k : Nat) (hoff : off = 8 * k) (hk25 : k + 1 ≤ 25)
    (hk200 : off + 8 ≤ 200) (src : ExpHOL 64)
    (hv : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), ptxPhase2CRInv s →
      evalAt s src = none ∨ ∃ w, evalAt s src = some (.val (.word w))) :
    Hoare ptxPhase2EInv
      (.store (.op .add [.var .local (ofString "te"), .const off]) src)
      (fun r s => r = none → ptxPhase2EInv s) := by
  apply Hoare.store_fall
  intro F s x v mem hp hx hv' hst
  rcases hv s hp.1 with hnone | ⟨w, hw⟩
  · rw [hnone] at hv'; exact absurd hv' (by simp)
  · have hvv : v = .val (.word w) := Option.some.inj (hv'.symm.trans hw)
    subst v
    obtain ⟨hdom, _, hmem⟩ := panMemStoresHOL_word_spec
      (by simpa only [flattenHOL] using hst)
    refine ⟨ptxPhase2CRInv_store_mem hp.1 hdom
      (phase2_te_offset_inside hp.1.1.1.1 off hk200 hx) hmem, ?_⟩
    obtain ⟨wte, hwte⟩ := hp.1.1.1.1.2.1
    have hl : locN s "te" = wte.toNat := by simp [locN, hwte]
    have he : x = wte + BitVec.ofNat 64 off := by
      simpa [evalAt, evalHOLExact, evalListHOLExact, hwte, valueIsWord, valueWord,
        panOpHOL, wordOpHOL, wordOp, List.foldr, BitVec.ofNat_mul, hoff] using hx.symm
    have hx' : x = BitVec.ofNat 64 (locN s "te" + 8 * k) := by
      simp [he, hl, BitVec.ofNat_add, hoff]
    rw [hx'] at hst
    exact (ptxPhase2_teStoreX_words (flattenHOL (.val (.word w))) ⟨hp.1.1.1, hp.2⟩ k
      (by simp [flattenHOL]; omega) hst).2

theorem ptxPhase2E_store_al_addrs : Hoare ptxPhase2EInv
    (.store (.op .add [.var .local (ofString "te"), .const 96])
      (.var .local (ofString "al_addrs")))
    (fun r s => r = none → ptxPhase2EInv s) := by
  apply ptxPhase2E_offset_hoare 96 12 (by decide) (by omega) (by dsimp; omega)
  intro F s hp
  obtain ⟨w, hw⟩ := hp.2.2.2.1
  exact Or.inr ⟨w, phase2_teSuf_eval_var hw⟩

theorem ptxPhase2E_store_nal_succ : Hoare ptxPhase2EInv
    (.store (.op .add [.var .local (ofString "te"), .const 104])
      (.op .add [.var .local (ofString "nal"), .const 1]))
    (fun r s => r = none → ptxPhase2EInv s) := by
  apply ptxPhase2E_offset_hoare 104 13 (by decide) (by omega) (by dsimp; omega)
  intro F s hp
  obtain ⟨w, hw⟩ := hp.1.2.1
  exact Or.inr ⟨_, phase2_teSuf_eval_add_const hw 1⟩

theorem ptxPhase2E_store_al_keys : Hoare ptxPhase2EInv
    (.store (.op .add [.var .local (ofString "te"), .const 112])
      (.var .local (ofString "al_keys")))
    (fun r s => r = none → ptxPhase2EInv s) := by
  apply ptxPhase2E_offset_hoare 112 14 (by decide) (by omega) (by dsimp; omega)
  intro F s hp
  obtain ⟨w, hw⟩ := hp.2.2.1
  exact Or.inr ⟨w, phase2_teSuf_eval_var hw⟩

theorem ptxPhase2E_store_nkeys : Hoare ptxPhase2EInv
    (.store (.op .add [.var .local (ofString "te"), .const 120])
      (.var .local (ofString "nkeys")))
    (fun r s => r = none → ptxPhase2EInv s) := by
  apply ptxPhase2E_offset_hoare 120 15 (by decide) (by omega) (by dsimp; omega)
  intro F s hp
  obtain ⟨w, hw⟩ := hp.2.1
  exact Or.inr ⟨w, phase2_teSuf_eval_var hw⟩

theorem ptxPhase2E_store_load_one (off off' k : Nat) (hoff : off = 8 * k)
    (hk25 : k + 1 ≤ 25) (hk200 : off + 8 ≤ 200) : Hoare ptxPhase2EInv
    (.store (.op .add [.var .local (ofString "te"), .const off])
      (.load .one (.op .add [.var .local (ofString "tx"), .const off'])))
    (fun r s => r = none → ptxPhase2EInv s) := by
  apply ptxPhase2E_offset_hoare off k hoff hk25 hk200
  intro F s hp
  exact phase2_teSuf_load_one_cases s _

theorem ptxPhase2E_store_const_one : Hoare ptxPhase2EInv
    (.store (.op .add [.var .local (ofString "te"), .const 160]) (.const 1))
    (fun r s => r = none → ptxPhase2EInv s) := by
  apply ptxPhase2E_offset_hoare 160 20 (by decide) (by omega) (by dsimp; omega)
  intro F s hp
  exact Or.inr ⟨_, phase2_teSuf_eval_const s 1⟩

theorem ptxPhase2E_store_index : Hoare ptxPhase2EInv
    (.store (.op .add [.var .local (ofString "te"), .const 168])
      (.var .local (ofString "index")))
    (fun r s => r = none → ptxPhase2EInv s) := by
  apply ptxPhase2E_offset_hoare 168 21 (by decide) (by omega) (by dsimp; omega)
  intro F s hp
  obtain ⟨w, hw⟩ := hp.1.1.1.1.2.scalar "index" (by simp)
  exact Or.inr ⟨w, phase2_teSuf_eval_var hw⟩

theorem ptxPhase2E_store_intrinsic_zero : Hoare ptxPhase2EInv
    (.store (.op .add [.var .local (ofString "te"), .const 184])
      (.rfield 0 (.var .local (ofString "intrinsic"))))
    (fun r s => r = none → ptxPhase2EInv s) := by
  apply ptxPhase2E_offset_hoare 184 23 (by decide) (by omega) (by dsimp; omega)
  intro F s hp
  obtain ⟨a, b, c, hw⟩ := hp.1.1.1.1.2.intrinsic
  exact Or.inr ⟨a, phase2_teSuf_eval_rfield_zero hw⟩

theorem ptxPhase2E_store_intrinsic_one : Hoare ptxPhase2EInv
    (.store (.op .add [.var .local (ofString "te"), .const 192])
      (.rfield 1 (.var .local (ofString "intrinsic"))))
    (fun r s => r = none → ptxPhase2EInv s) := by
  apply ptxPhase2E_offset_hoare 192 24 (by decide) (by omega) (by dsimp; omega)
  intro F s hp
  obtain ⟨a, b, c, hw⟩ := hp.1.1.1.1.2.intrinsic
  exact Or.inr ⟨b, phase2_teSuf_eval_rfield_one hw⟩

theorem ptxPhase2E_store_txh : Hoare ptxPhase2ETxh
    (.store (.op .add [.var .local (ofString "te"), .const 176])
      (.var .local (ofString "txh")))
    (fun r s => r = none → ptxPhase2ETxh s) := by
  apply Hoare.store_fall
  intro F s x v mem hp hx hv' hst
  obtain ⟨w, hw⟩ := hp.2
  have hvv : v = .val (.word w) :=
    Option.some.inj (hv'.symm.trans (phase2_teSuf_eval_var hw))
  subst v
  obtain ⟨hdom, _, hmem⟩ := panMemStoresHOL_word_spec
    (by simpa only [flattenHOL] using hst)
  refine ⟨⟨ptxPhase2CRInv_store_mem hp.1.1 hdom
    (phase2_te_offset_inside hp.1.1.1.1.1 176 (by dsimp; omega) hx) hmem, ?_⟩, w, hw⟩
  obtain ⟨wte, hwte⟩ := hp.1.1.1.1.1.2.1
  have hl : locN s "te" = wte.toNat := by simp [locN, hwte]
  have he : x = wte + BitVec.ofNat 64 176 := by
    simpa [evalAt, evalHOLExact, evalListHOLExact, hwte, valueIsWord, valueWord,
      panOpHOL, wordOpHOL, wordOp, List.foldr, BitVec.ofNat_mul] using hx.symm
  have hx' : x = BitVec.ofNat 64 (locN s "te" + 176) := by
    simp [he, hl, BitVec.ofNat_add]
  rw [hx'] at hst
  exact (ptxPhase2_teStoreX_words (flattenHOL (.val (.word w))) ⟨hp.1.1.1.1, hp.1.2⟩ 22
    (by simp [flattenHOL]) hst).2

/-- The region-E invariant reads only the listed caller locals. -/
theorem localsOnly_ptxPhase2EInv : LocalsOnly phase2_teSufNames ptxPhase2EInv := by
  intro _F s locals k hl hp
  exact ptxPhase2EInv_with_locals s locals k hl hp

/-! ## Read-only call resumes and the flag-probe conditionals -/

/-- Read-only calls preserve the region-E invariant. -/
theorem ptxPhase2E_ro_resume {fname name : MlS}
    (hro : ReadOnlyFn fname)
    (hne : ∀ n ∈ phase2_teSufNames, ofString n ≠ name)
    (args : List (ExpHOL 64)) :
    DecCallResumeOn ptxPhase2EInv ptxPhase2EInv name fname args := by
  intro F s vs body callee ret v post hc hp ha hl hb
  have hr := R16Shards.PtxP1.funSpec_at_lookup hro s hc vs body callee ret hl
    (guestInv_callEntry s callee hp.1.1.1.1.1.1.1.1.1.1.1) (by rw [hb]; simp)
  rw [hb] at hr
  have he := hr (Or.inl ⟨v, rfl⟩)
  dsimp only at he
  have he' : ({ post with locals := s.locals } : PanSemStateFiniteExact 64 F) =
      { s with clock := post.clock } := by rw [he]; rfl
  apply LocalsOnly.setVar localsOnly_ptxPhase2EInv hne v
  rw [he']
  exact ptxPhase2EInv_with_locals s s.locals post.clock (fun _ _ => rfl) hp

theorem ptxPhase2E_isb_resume (h : PtxCallees) :
    DecCallResumeOn ptxPhase2EInv ptxPhase2EInv (ofString "isb")
      (ofString "tx_is_blob") [.var .local (ofString "tx")] :=
  ptxPhase2E_ro_resume h.ro_tx_is_blob (by decide) _

theorem ptxPhase2E_issc_resume (h : PtxCallees) :
    DecCallResumeOn ptxPhase2EInv ptxPhase2EInv (ofString "issc")
      (ofString "tx_is_setcode") [.var .local (ofString "tx")] :=
  ptxPhase2E_ro_resume h.ro_tx_is_setcode (by decide) _

/-- The blob-branch conditional stores. -/
theorem ptxPhase2E_blob_ite : Hoare ptxPhase2EInv
    (.ite (.cmp .notEqual (.var .local (ofString "isb")) (.const 0))
      (.seq
        (.store (.op .add [.var .local (ofString "te"), .const 128])
          (.load .one (.op .add [.var .local (ofString "tx"), .const 256])))
        (.store (.op .add [.var .local (ofString "te"), .const 136])
          (.load .one (.op .add [.var .local (ofString "tx"), .const 264]))))
      .skip)
    (fun r s => r = none → ptxPhase2EInv s) := by
  apply Hoare.ite
  · apply Hoare.seq_fall
    · refine ⟨fun s hc hp hn hr => ?_⟩
      exact (ptxPhase2E_store_load_one 128 256 16 (by decide) (by omega)
        (by dsimp; omega)).run s hc hp.1 hn hr
    · exact ptxPhase2E_store_load_one 136 264 17 (by decide) (by omega) (by dsimp; omega)
  · exact Hoare.skip (fun s hp _ => hp.1)
  · intro F s hp hr
    exact absurd hr (by simp)

/-- The setcode-branch conditional stores. -/
theorem ptxPhase2E_setcode_ite : Hoare ptxPhase2EInv
    (.ite (.cmp .notEqual (.var .local (ofString "issc")) (.const 0))
      (.seq
        (.store (.op .add [.var .local (ofString "te"), .const 144])
          (.load .one (.op .add [.var .local (ofString "tx"), .const 272])))
        (.store (.op .add [.var .local (ofString "te"), .const 152])
          (.load .one (.op .add [.var .local (ofString "tx"), .const 280]))))
      .skip)
    (fun r s => r = none → ptxPhase2EInv s) := by
  apply Hoare.ite
  · apply Hoare.seq_fall
    · refine ⟨fun s hc hp hn hr => ?_⟩
      exact (ptxPhase2E_store_load_one 144 272 18 (by decide) (by omega)
        (by dsimp; omega)).run s hc hp.1 hn hr
    · exact ptxPhase2E_store_load_one 152 280 19 (by decide) (by omega) (by dsimp; omega)
  · exact Hoare.skip (fun s hp _ => hp.1)
  · intro F s hp hr
    exact absurd hr (by simp)

/-! ## Call-entry guards -/

/-- Call-entry guard for any callee reached from a region-E state. -/
theorem ptxPhase2E_callEntry {fname : MlS} (arguments : List (ExpHOL 64)) :
    CallEntryOn ptxPhase2EInv GuestInv fname arguments := by
  intro F state values body callee ret hcode hP hargs hl
  exact guestInv_callEntry state callee hP.1.1.1.1.1.1.1.1.1.1.1

/-- Call-entry guard for any callee reached from a hash-ready state. -/
theorem ptxPhase2EHash_callEntry {fname : MlS} (arguments : List (ExpHOL 64)) :
    CallEntryOn ptxPhase2EHashReady GuestInv fname arguments := by
  intro F state values body callee ret hcode hP hargs hl
  exact guestInv_callEntry state callee hP.1.1.1.1.1.1.1.1.1.1.1.1

/-! ## The hash-buffer allocation (position 64) -/

/-- The hash-buffer allocation (position 64): the region-E invariant
survives, the fresh 32-byte buffer is exported with its separation
geometry, and the auxiliary conjunct rides through because `alloc`
leaves memory and every non-`heap_ptr` global untouched. -/
theorem ptxPhase2E_alloc_txh (h : PtxCallees) :
    DecCallResumeOn ptxPhase2EInv ptxPhase2EHashReady
      (ofString "txh") (ofString "alloc") [.const 0x20] := by
  intro F s vs body callee ret v post hc hp ha hl hb
  have hb0 := hb
  have hAR : ArenaReady s := hp.1.1.1.1.1.1.1.1.1.1
  have hGI : GuestInv s := hp.1.1.1.1.1.1.1.1.1.1.1
  -- the alloc argument is the constant 32
  obtain ⟨v₀, he₀, hn₀⟩ := R16Shards.PtxP1.params_one_value s (ofString "alloc")
    (ofString "n") .one _ .one (by rw [hc]; exact R16Shards.PtxP1.lookup_alloc)
    (.const 0x20) vs body callee ret ha hl
  have h3 : evalAt s (.const 0x20) = some (.val (.word (BitVec.ofNat 64 32))) :=
    phase2_teSuf_eval_const s 32
  have hv₀ : v₀ = .val (.word (BitVec.ofNat 64 32)) :=
    Option.some.inj (he₀.symm.trans h3)
  have hcn : locN (callEntryStateHOLFinite s callee) "n" = 32 := by
    simp [locN, callEntryStateHOLFinite, hn₀, hv₀]
  have hround : (32 + 7) / 8 * 8 = 32 := by decide
  -- fresh block from the returns spec
  have hr := R16Shards.PtxP1.funSpec_at_lookup h.rt_alloc s hc vs body callee ret hl
    ((arenaReady_with_locals s callee (s.clock - 1)).mpr hAR) (by rw [hb]; simp)
  rw [hb] at hr
  obtain ⟨w, hvw, _, _, hf⟩ := hr v rfl
  rw [hcn] at hf
  have hfs := phase2_fresh_separation s post callee w.toNat 32 hp.1.1 hf
  have hf' : w.toNat % 8 = 0 ∧
      Inside (w.toNat, 32) (globN (callEntryStateHOLFinite s callee) "heap_ptr")
        (globN post "heap_ptr") ∧ WordsOK post (w.toNat, 32) := by
    simpa only [FreshBlock, hround] using hf
  -- master world step
  have hWORLD : WorldOK s := hp.1.1.1.1.1.1.1.1.1
  have hw := R16Shards.PtxP1.funSpec_at_lookup h.wk_alloc s hc vs body callee ret hl
    (R16Shards.PtxP1.worldOK_callEntry hWORLD callee) (by rw [hb]; simp)
  rw [hb] at hw
  have hs := hw (Or.inl ⟨_, rfl⟩)
  have hhp : globN s "heap_ptr" ≤ globN post "heap_ptr" := hs.2.1
  -- the al_addrs-bundle witness
  obtain ⟨S₃, Nd₃, hW₃, hT₃, hbuf₃, hde₃⟩ := hp.1.2.2.2.2.1
  have hWe₃ := (worldTypedWith_with_locals s callee (s.clock - 1) S₃ Nd₃).mpr hW₃
  obtain ⟨S₃', Nd₃', -, hW₃', hgrow₃, hframe₃, hQ₃⟩ :=
    hs.2.2.2.2 S₃ Nd₃ hWe₃ (by simp [IvlsDisj])
  obtain ⟨w₃, hw₃, hRA₃⟩ := hQ₃ v rfl
  rw [hvw, ValueHOL.val.injEq, HolWordLab.word.injEq] at hw₃
  rw [← hw₃] at hRA₃
  simp only [hcn, hround] at hRA₃
  have hbufout₃ : IvlsDisj [(locN s "al_addrs", (locN s "nal" + 1) * 8)]
      (worldOwned post S₃' Nd₃') :=
    phase2_packed_owned_growth s post _ _ _ hp.1.2.2.2.2.2 hgrow₃ hbuf₃
  -- the transaction header words survive (no writes outside the world)
  have htx8 : (locN s "tx") % 8 = 0 := hT₃.1.1.1
  have htxin : Inside (locN s "tx", 384) InitE.sourceBase (globN s "heap_ptr") := hT₃.1.2.1
  have htxow : ∀ j ∈ worldOwned s S₃ Nd₃, Disj (locN s "tx", 384) j :=
    fun j hj => hT₃.2.1 _ (by simp) j hj
  have htxu := heap_ivl_survives_step hAR.2 hhp
    (worldOwned_zero_aligned hW₃) (R := []) (by simp) hgrow₃ hframe₃
    htx8 (by norm_num) htxin htxow (by simp)
  obtain ⟨_, _, hu₂⟩ := htxu
  have hhi : locN s "tx" + 384 ≤ 2 ^ 64 :=
    (ivl_allocated_bound hAR.2 (Or.inl htxin)).2
  have hmem216 : memW post (locN s "tx" + 216) = memW s (locN s "tx" + 216) :=
    memW_eq_of_ivlUnhit hu₂ (by have := htx8; omega) hhi (by omega)
  have hmem208 : memW post (locN s "tx" + 208) = memW s (locN s "tx" + 208) :=
    memW_eq_of_ivlUnhit hu₂ (by have := htx8; omega) hhi (by omega)
  -- the out state
  let out := setVarHOLFinite (ofString "txh") v { post with locals := s.locals }
  show ptxPhase2EHashReady out
  have hPVS : PtxValidatedStrong out := by
    exact phase2_teSuf_alloc_validated h s vs body callee ret v post hc
      hp.1.1.1.1.1 ha hl hb0
  have hGIout : GuestInv out := hPVS.1.1.1.1.1.1
  have hptxh : locN out "txh" = w.toNat := by
    simp [out, locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hvw]
  have hloc {name : String} (hne : ofString "txh" ≠ ofString name) :
      locN out name = locN s name := by
    simp [out, locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne]
  have hluk {name : String} (hne : ofString "txh" ≠ ofString name) :
      out.locals.lookup (ofString name) = s.locals.lookup (ofString name) := by
    simp [out, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne]
  have hT₃' := R16Shards.PtxP1.txAccessListOK_survives_step hAR hs.1.1 hhp hW₃
    (R := []) (by simp) hgrow₃ hframe₃ hT₃ (by simp) (by simp)
    (locals := out.locals)
    (by simp [out, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "txh" ≠ ofString "tx" by decide])
  have hWT₃ : WorldTypedWith out S₃' Nd₃' :=
    (worldTypedWith_with_locals post out.locals post.clock S₃' Nd₃').mpr hW₃'
  have hTAL₃ : TxAccessListAt out S₃' Nd₃' (locN out "tx") := hT₃'
  have hte₃' := heap_ivl_survives_step hAR.2 hhp
    (worldOwned_zero_aligned hW₃) (R := []) (by simp) hgrow₃ hframe₃
    hp.1.1.1.1.2.2.2.1 (by norm_num) hp.1.1.1.1.2.2.1
    (fun j hj => hde₃ _ (by simp) j hj) (by simp)
  -- the X part: alloc keeps memory and every non-heap_ptr global
  have hbody : body = InitECandidate.Solver.GuestTrapAndLookup.sourceFnBody
      Guest.Software.guestFn_alloc :=
    InitECandidate.Solver.PanRunBounded.lookupCodeHOLFinite_installed_body s.code.lookup
      (ofString "alloc") [(ofString "n", .one)]
      (InitECandidate.Solver.GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_alloc) body
      .one ret vs callee
      (by rw [hc]; exact InitECandidate.Solver.GuestTrapAndLookup.lookup_alloc) hl
  rw [hbody] at hb0
  have hA' : ArenaReady (callEntryStateHOLFinite s callee) :=
    (arenaReady_with_locals s callee (s.clock - 1)).mpr hAR
  obtain ⟨hpw, hhpw⟩ := hA'.2.2.2.2.2.2.2.2.2 "heap_ptr" (by simp [guestGlobalNames])
  have hcode' : (callEntryStateHOLFinite s callee).code = originalRuntimeCode := hc
  have hnloc : (callEntryStateHOLFinite s callee).locals.lookup (ofString "n") =
      some (.val (.word (BitVec.ofNat 64 32))) := by
    have hle : (callEntryStateHOLFinite s callee).locals = callee := rfl
    rw [hle, hn₀, hv₀]
  have hout1 : (evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
      (InitECandidate.Solver.GuestTrapAndLookup.sourceFnBody
        Guest.Software.guestFn_alloc)).1 = some (.returned v) := by rw [hb0]
  obtain ⟨-, -, -, hEq⟩ := InitECandidate.Solver.Wave8Contracts.M27.alloc_body_run
    (callEntryStateHOLFinite s callee) hpw (BitVec.ofNat 64 32) hcode' hhpw hnloc v hout1
  have hpost : post = (evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
      (InitECandidate.Solver.GuestTrapAndLookup.sourceFnBody
        Guest.Software.guestFn_alloc)).2 := by rw [hb0]
  have hmemF : ∀ a, post.memory a = s.memory a := by
    intro a
    rw [hpost, hEq]
    rfl
  have hgl (m : MlS) (hm : m ≠ ofString "heap_ptr") :
      post.globals.lookup m = s.globals.lookup m := by
    rw [hpost, hEq]
    have hentry : (callEntryStateHOLFinite s callee).globals = s.globals := rfl
    rw [hentry]
    show (s.globals.update (ofString "heap_ptr", _)).lookup m = s.globals.lookup m
    simp [HolFiniteMapExact.lookup_update, FUPDATE, hm.symm]
  have hboG : globN post "bo" = globN s "bo" := by
    unfold globN
    rw [hgl (ofString "bo") (by decide)]
  have hjcG : globN post "journal_cap" = globN s "journal_cap" := by
    unfold globN
    rw [hgl (ofString "journal_cap") (by decide)]
  have hcells : ∀ k ∈ ([24, 32, 40, 72, 80] : List Nat),
      memW { post with locals := s.locals } (globN s "bo" + k) =
      memW s (globN s "bo" + k) := by
    intro k _
    unfold memW
    rw [hmemF (BitVec.ofNat 64 (globN s "bo" + k))]
  have hXpost : PtxPhase2X { post with locals := s.locals } :=
    ptxPhase2X_of_cells hp.2
      (ptxPhase2_txBacking_of_mem_eq hp.2.2.1 hboG hmemF) rfl hboG hjcG rfl hcells
  have hXout : PtxPhase2X out := by
    refine ptxPhase2X_setVar_other _ v (fun n hn => ?_) hXpost
    have hne : ofString "txh" ≠ ofString n := by
      simp only [ptxPhase2XNames, List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact hne.symm
  -- reassemble the region-E invariant and the geometry at the out state
  obtain ⟨S₁, Nd₁, hW₁, hT₁, hd₁, htxte₁, hrec₁⟩ := hp.1.1.1.2
  obtain ⟨wte, hwtew⟩ := hp.1.1.1.1.2.1
  obtain ⟨wnal, hwnalw⟩ := hp.1.1.2.1
  obtain ⟨wnkeys, hwnkeysw⟩ := hp.1.2.1
  obtain ⟨walkeys, hwalkeysw⟩ := hp.1.2.2.1
  obtain ⟨waladdrs, hwaladdrsw⟩ := hp.1.2.2.2.1
  refine ⟨⟨⟨⟨⟨⟨hPVS, ⟨wte, ?_⟩, ?_, ?_, ?_, S₃', Nd₃', hWT₃, ?_⟩,
    S₃', Nd₃', hWT₃, hTAL₃, ?_, ?_, ?_⟩, ⟨wnal, ?_⟩, ?_⟩,
    ⟨wnkeys, ?_⟩, ⟨walkeys, ?_⟩, ⟨waladdrs, ?_⟩,
    ⟨S₃', Nd₃', hWT₃, hTAL₃, ?_, ?_⟩, ?_⟩, hXout⟩,
    ⟨w, ?_, hf'.1, ?_, ?_, ?_, ⟨S₃', Nd₃', hWT₃, hTAL₃, ?_, ?_, ?_, ?_⟩⟩⟩
  · rw [hluk (show ofString "txh" ≠ ofString "te" by decide)]
    exact hwtew
  · rw [hloc (show ofString "txh" ≠ ofString "te" by decide)]
    exact ⟨hp.1.1.1.1.2.2.1.1, hp.1.1.1.1.2.2.1.2.trans hhp⟩
  · rw [hloc (show ofString "txh" ≠ ofString "te" by decide)]
    exact hp.1.1.1.1.2.2.2.1
  · rw [hloc (show ofString "txh" ≠ ofString "te" by decide)]
    exact wordsOK_transfer hGI hGIout hp.1.1.1.1.2.2.2.2.1
  · rw [hloc (show ofString "txh" ≠ ofString "te" by decide)]
    intro i hi j hj
    simp only [List.mem_singleton] at hi
    subst i
    exact hte₃'.2.1 j hj
  · rw [hloc (show ofString "txh" ≠ ofString "te" by decide)]
    intro i hi j hj
    simp only [List.mem_singleton] at hi
    subst i
    exact hte₃'.2.1 j hj
  · rw [hloc (show ofString "txh" ≠ ofString "tx" by decide),
      hloc (show ofString "txh" ≠ ofString "te" by decide)]
    exact htxte₁
  · rw [hloc (show ofString "txh" ≠ ofString "tx" by decide),
      hloc (show ofString "txh" ≠ ofString "te" by decide)]
    intro hn
    change Disj (memW post (locN s "tx" + 208), 24 * memW post (locN s "tx" + 216))
      (locN s "te", 200)
    change 0 < memW post (locN s "tx" + 216) at hn
    rw [hmem216] at hn
    rw [hmem208, hmem216]
    exact hrec₁ hn
  · rw [hluk (show ofString "txh" ≠ ofString "nal" by decide)]
    exact hwnalw
  · rw [hloc (show ofString "txh" ≠ ofString "nal" by decide),
      hloc (show ofString "txh" ≠ ofString "tx" by decide)]
    rcases hp.1.1.2.2 with h0 | hn
    · exact Or.inl h0
    · refine Or.inr ?_
      change locN s "nal" = memW post (locN s "tx" + 216)
      rw [hn]
      exact hmem216.symm
  · rw [hluk (show ofString "txh" ≠ ofString "nkeys" by decide)]
    exact hwnkeysw
  · rw [hluk (show ofString "txh" ≠ ofString "al_keys" by decide)]
    exact hwalkeysw
  · rw [hluk (show ofString "txh" ≠ ofString "al_addrs" by decide)]
    exact hwaladdrsw
  · rw [hloc (show ofString "txh" ≠ ofString "al_addrs" by decide),
      hloc (show ofString "txh" ≠ ofString "nal" by decide)]
    exact hbufout₃
  · rw [hloc (show ofString "txh" ≠ ofString "te" by decide)]
    intro i hi j hj
    simp only [List.mem_singleton] at hi
    subst i
    exact hte₃'.2.1 j hj
  · rw [hloc (show ofString "txh" ≠ ofString "al_addrs" by decide),
      hloc (show ofString "txh" ≠ ofString "nal" by decide)]
    exact ⟨hp.1.2.2.2.2.2.1, hp.1.2.2.2.2.2.2.trans hhp⟩
  · simp [out, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hvw]
  · rw [hloc (show ofString "txh" ≠ ofString "te" by decide)]
    exact hfs.1
  · rw [hloc (show ofString "txh" ≠ ofString "tx" by decide)]
    exact hfs.2.1
  · intro hpos
    change 0 < memW post (locN s "tx" + 216) at hpos
    rw [hmem216] at hpos
    obtain ⟨-, hrb⟩ := (hT₁.2.2 hpos).1
    refine Or.inr (Or.inr (Or.inl ?_))
    change memW post (locN s "tx" + 208) + 24 * memW post (locN s "tx" + 216) ≤ w.toNat
    rw [hmem208, hmem216]
    have hwge : globN s "heap_ptr" ≤ w.toNat := hf'.2.1.1
    omega
  · rw [hloc (show ofString "txh" ≠ ofString "al_addrs" by decide),
      hloc (show ofString "txh" ≠ ofString "nal" by decide)]
    exact hbufout₃
  · rw [hloc (show ofString "txh" ≠ ofString "te" by decide)]
    intro i hi j hj
    simp only [List.mem_singleton] at hi
    subst i
    exact hte₃'.2.1 j hj
  · rw [hptxh]
    exact hRA₃
  · rw [hloc (show ofString "txh" ≠ ofString "al_addrs" by decide),
      hloc (show ofString "txh" ≠ ofString "nal" by decide)]
    exact ⟨hp.1.2.2.2.2.2.1, hp.1.2.2.2.2.2.2.trans hhp⟩

/-! ## The keccak256 hash call (position 65) -/

/-- The keccak256 hash call (position 65): the region-E invariant survives
with the caller's locals restored. The CRInv part is the frozen replay
minus the sender witness; the X part rides on the
`Keccak256.funByteEff_keccak256` spec, whose writes are confined to the
two keccak buffers and the fresh hash block, all disjoint from the
block-out record. -/
theorem ptxPhase2E_keccak_txh (h : PtxCallees) :
    Hoare ptxPhase2EHashReady
      (.call (some (none, none)) (ofString "keccak256")
        [.rfield 0 (.var .local (ofString "enc")),
         .rfield 1 (.var .local (ofString "enc")),
         .var .local (ofString "txh")])
      (fun r t => r = none → ptxPhase2ETxh t) := by
  refine ⟨fun {F} s hc hp hnt hr => ?_⟩
  rw [evaluateHOLFiniteState_call] at hr ⊢
  rcases ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.rfield 0 (.var .local (ofString "enc")),
       .rfield 1 (.var .local (ofString "enc")),
       .var .local (ofString "txh")] with _ | vs
  · rw [ha] at hr; simp at hr
  · simp only [ha] at hr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "keccak256") vs with _ | ⟨body, callee, ret⟩
    · simp [hl] at hr
    · simp only [hl] at hr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hr
      · simp only [hz, ↓reduceIte] at hr ⊢
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨res, post⟩
        simp only [hb] at hr ⊢
        cases res with
        | none => simp at hr
        | some r =>
          cases r with
          | returned v =>
            dsimp only at hr ⊢
            split at hr
            · rename_i hsh
              rw [if_pos hsh]
              -- the assembled context: call-run, geometry, witnesses
              have hAR : ArenaReady s := hp.1.1.1.1.1.1.1.1.1.1.1
              have hGI : GuestInv s := hp.1.1.1.1.1.1.1.1.1.1.1.1
              have hWORLD : WorldOK s := hp.1.1.1.1.1.1.1.1.1.1
              have hlook : originalRuntimeCode.lookup (ofString "keccak256") =
                  some ([(ofString "p", .one), (ofString "n", .one), (ofString "out", .one)],
                    (sourceFunctionEntry Guest.Software.guestFn_keccak256).2.2.1,
                    (sourceFunctionEntry Guest.Software.guestFn_keccak256).2.2.2) :=
                InitECandidate.Solver.GuestTrapAndLookup.lookup_of_guestAst_getElem 103
                  (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_keccak256) rfl
              obtain ⟨v₁, v₂, v₃, he₁, he₂, he₃, hp₁, hp₂, hrcallee⟩ :=
                R16Shards.PtxP1.params_three_values s (ofString "keccak256")
                (ofString "p") (ofString "n") (ofString "out") .one .one .one _ .one
                (by rw [hc]; exact hlook)
                (.rfield 0 (.var .local (ofString "enc")))
                (.rfield 1 (.var .local (ofString "enc")))
                (.var .local (ofString "txh"))
                vs body callee ret ha hl
              obtain ⟨w, hwl, hw8, hte, htx, hrecw, hwit⟩ := hp.2
              have hv₃ : v₃ = .val (.word w) := Option.some.inj (he₃.symm.trans hwl)
              have hout : locN (callEntryStateHOLFinite s callee) "out" = w.toNat := by
                simp only [locN, callEntryStateHOLFinite, hrcallee, hv₃]
              have hvs3 : vs = [v₁, v₂, v₃] := by
                have ha' := ha
                rw [evalListHOLFinite_eq_toExact] at ha'
                simp only [evalListHOLExact, he₁, he₂, he₃] at ha'
                exact (Option.some.inj ha').symm
              -- master world step, re-anchored at the caller
              have hw := R16Shards.PtxP1.funSpec_at_lookup h.wk_keccak256 s hc vs body callee ret hl
                (R16Shards.PtxP1.worldOK_callEntry hWORLD callee) (by rw [hb]; simp)
              rw [hb] at hw
              have hstep := hw (Or.inl ⟨v, rfl⟩)
              have hs := R13Shards.worldStep_with_locals hstep s.locals s.clock
              change WorldStep (fun _ => [(locN (callEntryStateHOLFinite s callee) "out", 32),
                bufferRegion s ("keccak_pad", 136), bufferRegion s ("keccak_st", 200)]) _ _ _ s _ post at hs
              rw [hout] at hs
              have hhp : globN s "heap_ptr" ≤ globN post "heap_ptr" := hs.2.1
              -- the al_addrs bundle witness at the pre state
              obtain ⟨S₃, Nd₃, hW₃, hT₃, hbuf₃, hde₃, hp32₃, hin₃⟩ := hwit
              have hltxh : locN s "txh" = w.toNat := by simp [locN, hwl]
              have hp32₃' : IvlsDisj [(w.toNat, 32)] (worldOwned s S₃ Nd₃) := by
                rw [← hltxh]; exact hp32₃
              -- safety of the written regions against the typed world
              have hRT₃ : IvlsDisj [(w.toNat, 32), bufferRegion s ("keccak_pad", 136),
                  bufferRegion s ("keccak_st", 200)] (worldTypedIvls s S₃ Nd₃) := by
                intro i hi j hj
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
                rcases hi with rfl | rfl | rfl
                · exact phase2_packed_typed_of_owned s S₃ Nd₃ [(w.toNat, 32)] hp32₃'
                    (w.toNat, 32) (by simp) j hj
                · exact InitECandidate.Solver.Wave8GuestInv.bufferRegion_disj_le hW₃
                    ("keccak_pad", 136) (by decide) (by decide) 136 le_rfl j hj
                · exact InitECandidate.Solver.Wave8GuestInv.bufferRegion_disj_le hW₃
                    ("keccak_st", 200) (by decide) (by decide) 200 le_rfl j hj
              have hR0 : ∀ i ∈ [(w.toNat, 32), bufferRegion s ("keccak_pad", 136),
                  bufferRegion s ("keccak_st", 200)], i.2 = 0 → i.1 % 8 = 0 := by
                intro i hi
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
                rcases hi with rfl | rfl | rfl
                · simp
                · exact R16Shards.PtxP1.bufferRegion_zero_aligned s "keccak_pad" 136 (by decide)
                · exact R16Shards.PtxP1.bufferRegion_zero_aligned s "keccak_st" 200 (by decide)
              -- transaction header separation from the written regions
              have htxow : ∀ j ∈ worldOwned s S₃ Nd₃, Disj (locN s "tx", 384) j :=
                fun j hj => hT₃.2.1 _ (by simp) j hj
              have htx_R : ∀ i ∈ [(w.toNat, 32), bufferRegion s ("keccak_pad", 136),
                  bufferRegion s ("keccak_st", 200)], Disj (locN s "tx", 384) i := by
                intro i hi
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
                rcases hi with rfl | rfl | rfl
                · exact htx
                · exact R16Shards.PtxP1.heap_ivl_disj_bufferRegion_le htxow
                    ("keccak_pad", 136) (by decide) 136 le_rfl
                · exact R16Shards.PtxP1.heap_ivl_disj_bufferRegion_le htxow
                    ("keccak_st", 200) (by decide) 200 le_rfl
              have hrecs_R : 0 < memW s (locN s "tx" + 216) →
                  ∀ i ∈ [(w.toNat, 32), bufferRegion s ("keccak_pad", 136),
                    bufferRegion s ("keccak_st", 200)],
                    Disj (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216)) i := by
                intro hpos i hi
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
                rcases hi with rfl | rfl | rfl
                · exact hrecw hpos
                · exact R16Shards.PtxP1.heap_ivl_disj_bufferRegion_le
                    (fun j hj => (hT₃.2.2 hpos).2 _ (by simp) j hj)
                    ("keccak_pad", 136) (by decide) 136 le_rfl
                · exact R16Shards.PtxP1.heap_ivl_disj_bufferRegion_le
                    (fun j hj => (hT₃.2.2 hpos).2 _ (by simp) j hj)
                    ("keccak_st", 200) (by decide) 200 le_rfl
              -- the validated frame survives via the packaged world step
              have hTRS : TxReadyStrong { post with locals := s.locals } :=
                R16Shards.PtxP1.txReadyStrong_worldStep hs hAR
                  (R16Shards.PtxP1.txEnv_of_ready hp.1.1.1.1.1.1.1.1) hW₃ hT₃
                  (by decide) (by decide) (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])
                  (by simp) (by decide) hR0 hRT₃ htx_R hrecs_R
              have hGIpost : GuestInv post := hs.1.1
              have hARout : ArenaReady { post with locals := s.locals } :=
                (arenaReady_with_locals post s.locals post.clock).mpr hs.1
              have hGIout : GuestInv { post with locals := s.locals } := hARout.1
              have hPVS : PtxValidatedStrong { post with locals := s.locals } :=
                ⟨⟨hTRS, ⟨hp.1.1.1.1.1.1.1.2.1.1, hp.1.1.1.1.1.1.1.2.1.2.trans hhp⟩,
                  wordsOK_transfer hGI hGIout hp.1.1.1.1.1.1.1.2.2.1, hp.1.1.1.1.1.1.1.2.2.2⟩,
                ptxPhase2LocalShapes_restore s post hp.1.1.1.1.1.1.2⟩
              -- run the master at the bundle witness
              obtain ⟨S₃', Nd₃', -, hW₃', hgrow₃, hframe₃, -⟩ := hs.2.2.2.2 S₃ Nd₃ hW₃ hRT₃
              have hWT₃ : WorldTypedWith { post with locals := s.locals } S₃' Nd₃' :=
                (worldTypedWith_with_locals post s.locals post.clock S₃' Nd₃').mpr hW₃'
              have hT₃' := R16Shards.PtxP1.txAccessListOK_survives_step hAR hGIpost hhp hW₃
                hR0 hgrow₃ hframe₃ hT₃ htx_R hrecs_R (locals := s.locals) rfl
              have hTAL₃ : TxAccessListAt { post with locals := s.locals } S₃' Nd₃'
                  (locN { post with locals := s.locals } "tx") := hT₃'
              -- transaction header words survive
              have htx8 : (locN s "tx") % 8 = 0 := hT₃.1.1.1
              have htxin : Inside (locN s "tx", 384) InitE.sourceBase (globN s "heap_ptr") := hT₃.1.2.1
              have htxu := heap_ivl_survives_step hAR.2 hhp (worldOwned_zero_aligned hW₃) hR0
                hgrow₃ hframe₃ htx8 (by norm_num) htxin htxow htx_R
              obtain ⟨_, _, hu₂⟩ := htxu
              have hhi : locN s "tx" + 384 ≤ 2 ^ 64 :=
                (ivl_allocated_bound hAR.2 (Or.inl htxin)).2
              have hmem216 : memW post (locN s "tx" + 216) = memW s (locN s "tx" + 216) :=
                memW_eq_of_ivlUnhit hu₂ (by have := htx8; omega) hhi (by omega)
              have hmem208 : memW post (locN s "tx" + 208) = memW s (locN s "tx" + 208) :=
                memW_eq_of_ivlUnhit hu₂ (by have := htx8; omega) hhi (by omega)
              -- the hash buffer's separation from the te region
              have hteR : ∀ i ∈ [(w.toNat, 32), bufferRegion s ("keccak_pad", 136),
                  bufferRegion s ("keccak_st", 200)], Disj (locN s "te", 200) i := by
                intro i hi
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
                rcases hi with rfl | rfl | rfl
                · exact hte
                · exact R16Shards.PtxP1.heap_ivl_disj_bufferRegion_le (fun j hj => hde₃ _ (by simp) j hj)
                    ("keccak_pad", 136) (by decide) 136 le_rfl
                · exact R16Shards.PtxP1.heap_ivl_disj_bufferRegion_le (fun j hj => hde₃ _ (by simp) j hj)
                    ("keccak_st", 200) (by decide) 200 le_rfl
              have hte₃' := heap_ivl_survives_step hAR.2 hhp (worldOwned_zero_aligned hW₃) hR0
                hgrow₃ hframe₃ hp.1.1.1.1.1.2.2.2.1 (by norm_num) hp.1.1.1.1.1.2.2.1
                (fun j hj => hde₃ _ (by simp) j hj) hteR
              -- bundle buffers stay owned at the new witness
              have hbufout₃ : IvlsDisj [(locN s "al_addrs", (locN s "nal" + 1) * 8)]
                  (worldOwned post S₃' Nd₃') :=
                phase2_packed_owned_growth s post _ _ _ hin₃ hgrow₃ hbuf₃
              -- the X part: the keccak256 callee keeps the globals and
              -- writes only the two buffers plus the fresh hash block
              have hcr : evaluateHOLFiniteState s
                  (.call (some (none, none)) (ofString "keccak256")
                    [.rfield 0 (.var .local (ofString "enc")),
                     .rfield 1 (.var .local (ofString "enc")),
                     .var .local (ofString "txh")]) =
                  (none, { post with locals := s.locals }) := by
                rw [evaluateHOLFiniteState_call]
                simp only [ha, hl, hz, ↓reduceIte, hb]
                rw [if_pos hsh]
              have hntc : (evaluateHOLFiniteState s
                  (.call (some (none, none)) (ofString "keccak256")
                    [.rfield 0 (.var .local (ofString "enc")),
                     .rfield 1 (.var .local (ofString "enc")),
                     .var .local (ofString "txh")])).1 ≠ some .timeOut := by
                rw [hcr]; simp
              have horc : (evaluateHOLFiniteState s
                  (.call (some (none, none)) (ofString "keccak256")
                    [.rfield 0 (.var .local (ofString "enc")),
                     .rfield 1 (.var .local (ofString "enc")),
                     .var .local (ofString "txh")])).1 = none ∨
                  Resumes (evaluateHOLFiniteState s
                  (.call (some (none, none)) (ofString "keccak256")
                    [.rfield 0 (.var .local (ofString "enc")),
                     .rfield 1 (.var .local (ofString "enc")),
                     .var .local (ofString "txh")])).1 := by
                rw [hcr]; exact Or.inl rfl
              have hsub : ∀ vals : List (ValueHOL 64),
                  evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
                    [.rfield 0 (.var .local (ofString "enc")),
                     .rfield 1 (.var .local (ofString "enc")),
                     .var .local (ofString "txh")] = some vals →
                   ∀ i ∈ (fun vals G =>
                       [Keccak256.globBufIvl G "keccak_st" 200,
                         Keccak256.globBufIvl G "keccak_pad" 136,
                         (Keccak256.valWordNat (vals[2]?.getD (.rStruct [])), 32)]) vals s.globals,
                    0 < i.2 → ∃ j ∈ [bufferRegion s ("keccak_st", 200),
                      bufferRegion s ("keccak_pad", 136), (w.toNat, 32)],
                      j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2 := by
                intro vals hvs i hi _
                have hvl : vals = vs := Option.some.inj (hvs.symm.trans ha)
                subst hvl
                rw [hvs3, hv₃] at hi
                simp only [List.getElem?_cons_succ, List.getElem?_cons_zero,
                  Option.getD_some] at hi
                exact ⟨i, hi, le_rfl, le_rfl⟩
              obtain ⟨-, -, -, -, -, hglobEff, -, -, hcellf, -⟩ :=
                InitECandidate.Solver.Wave8GuestInv.R13Shards.Keccak256.call0_byteEff
                  InitECandidate.Solver.Wave8GuestInv.R13Shards.Keccak256.funByteEff_keccak256 s
                  [.rfield 0 (.var .local (ofString "enc")),
                   .rfield 1 (.var .local (ofString "enc")),
                   .var .local (ofString "txh")]
                  [bufferRegion s ("keccak_st", 200), bufferRegion s ("keccak_pad", 136),
                    (w.toNat, 32)]
                  hc hGI hsub hntc horc
              rw [hcr] at hglobEff hcellf
              have hboG : globN { post with locals := s.locals } "bo" = globN s "bo" := by
                unfold globN
                rw [hglobEff]
              have hjcG : globN { post with locals := s.locals } "journal_cap" =
                  globN s "journal_cap" := by
                unfold globN
                rw [hglobEff]
              have hboFix : (globN s "bo", 88) ∈ fixedObjects s := by
                simpa [hp.1.2.2.2.1.bo_nz] using typedRecord_mem_fixedObjects s (r := ("bo", 88)) (by decide)
              have hF : FixedTyped s := hW₃.2.2.1
              have hboHi : globN s "bo" + 88 ≤ 2 ^ 64 :=
                (ivl_allocated_bound hAR.2 (bo_words hF hp.1.2.2.2.1.bo_nz).1).2
              have hdisjRl : ∀ i ∈ [bufferRegion s ("keccak_st", 200),
                  bufferRegion s ("keccak_pad", 136), (w.toNat, 32)],
                  Disj (globN s "bo", 88) i := by
                intro i hi
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
                rcases hi with rfl | rfl | rfl
                · exact ptxPhase2E_disj_bo_keccakBuf s hF hp.1.2.2.2.1.bo_nz
                    (gn := ("keccak_st", 200)) (by simp [globalBuffers]) (by decide)
                · exact ptxPhase2E_disj_bo_keccakBuf s hF hp.1.2.2.2.1.bo_nz
                    (gn := ("keccak_pad", 136)) (by simp [globalBuffers]) (by decide)
                · have hboOwn : (globN s "bo", 88) ∈ worldOwned s S₃ Nd₃ := by
                    have h1 := hboFix
                    simp only [worldOwned, List.mem_append, List.not_mem_nil, or_false]
                    exact Or.inl (Or.inr h1)
                  exact disj_symm (hp32₃' _ (by simp) _ hboOwn)
              have hmemcell : ∀ a : Nat, globN s "bo" ≤ a → a + 8 ≤ globN s "bo" + 88 →
                  ({ post with locals := s.locals } : PanSemStateFiniteExact 64 F).memory
                    (BitVec.ofNat 64 a) = s.memory (BitVec.ofNat 64 a) := by
                intro a hlo hhib
                by_contra hm
                obtain ⟨i, hi, hpos⟩ := hcellf (BitVec.ofNat 64 a) hm
                have htoNat : (BitVec.ofNat 64 a).toNat = a :=
                  Nat.mod_eq_of_lt (by have := hboHi; omega)
                rw [htoNat] at hpos
                have hexcl : ∀ j, Disj (globN s "bo", 88) j →
                    ¬ Keccak256.CellHitsPos a j := by
                  intro j hd hc
                  unfold Disj at hd
                  simp only [Keccak256.CellHitsPos, CellHits] at hc
                  rcases hd with hz | hz | hl | hr <;> omega
                exact hexcl i (hdisjRl i hi) hpos
              have hcells : ∀ k ∈ ([24, 32, 40, 72, 80] : List Nat),
                  memW { post with locals := s.locals } (globN s "bo" + k) =
                  memW s (globN s "bo" + k) := by
                intro k hk
                have hk8 : k + 8 ≤ 88 := by
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
                  rcases hk with rfl | rfl | rfl | rfl | rfl <;> omega
                unfold memW
                rw [hmemcell (globN s "bo" + k) (by omega) (by omega)]
              have hXpost : PtxPhase2X { post with locals := s.locals } := by
                obtain ⟨-, -, hgb_rest, -, -⟩ := fixedObjects_disj_parts hF
                have hlst : ∀ k ∈ ([40, 72] : List Nat),
                    (memW s (globN s "bo" + k), 24) ∈ fixedObjects s := by
                  intro k hk'
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk'
                  rcases hk' with rfl | rfl
                  · simp [fixedObjects, blockOutObjects, hp.1.2.2.2.1.bo_nz,
                      hp.1.2.2.2.1.bo40]
                  · simp [fixedObjects, blockOutObjects, hp.1.2.2.2.1.bo_nz,
                      hp.1.2.2.2.1.bo72]
                have hmem_bo : ∀ k ∈ ([40, 72] : List Nat),
                    (memW s (globN s "bo" + k), 24) ∈ blockOutObjects s := by
                  intro k hk'
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk'
                  rcases hk' with rfl | rfl
                  · simp [blockOutObjects, hp.1.2.2.2.1.bo_nz, hp.1.2.2.2.1.bo40]
                  · simp [blockOutObjects, hp.1.2.2.2.1.bo_nz, hp.1.2.2.2.1.bo72]
                have hown : ∀ k ∈ ([40, 72] : List Nat),
                    (memW s (globN s "bo" + k), 24) ∈ worldOwned s S₃ Nd₃ := by
                  intro k hk'
                  have h1 := hlst k hk'
                  simp only [worldOwned, List.mem_append, List.not_mem_nil, or_false]
                  exact Or.inl (Or.inr h1)
                have hhb : ∀ k ∈ ([40, 72] : List Nat),
                    memW s (globN s "bo" + k) + 24 ≤ 2 ^ 64 := by
                  intro k hk'
                  rcases hF.1 _ (hlst k hk') with h0 | ⟨hal, -⟩
                  · simp at h0
                  · exact (ivl_allocated_bound hAR.2 hal).2
                have hhdmem : ∀ k ∈ ([40, 72] : List Nat),
                    ({ post with locals := s.locals } : PanSemStateFiniteExact 64 F).memory
                      (BitVec.ofNat 64 (memW s (globN s "bo" + k))) =
                    s.memory (BitVec.ofNat 64 (memW s (globN s "bo" + k))) := by
                  intro k hk'
                  have hdisjHd : ∀ i ∈ [bufferRegion s ("keccak_st", 200),
                      bufferRegion s ("keccak_pad", 136), (w.toNat, 32)],
                      Disj (memW s (globN s "bo" + k), 24) i := by
                    intro i hi
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
                    rcases hi with rfl | rfl | rfl
                    · exact disj_symm (hgb_rest _
                        (ptxPhase2E_gbs_mem s ("keccak_st", 200) (by simp [globalBuffers])) _
                        (List.mem_append_left (balObjects s)
                          (List.mem_append_right
                            [(if globN s "journal_cap" = 0 then 0 else globN s "journal",
                              32 * globN s "journal_cap")]
                            (hmem_bo k hk'))))
                    · exact disj_symm (hgb_rest _
                        (ptxPhase2E_gbs_mem s ("keccak_pad", 136) (by simp [globalBuffers])) _
                        (List.mem_append_left (balObjects s)
                          (List.mem_append_right
                            [(if globN s "journal_cap" = 0 then 0 else globN s "journal",
                              32 * globN s "journal_cap")]
                            (hmem_bo k hk'))))
                    · exact disj_symm (hp32₃' _ (by simp) _ (hown k hk'))
                  by_contra hm
                  obtain ⟨i, hi, hpos⟩ := hcellf
                    (BitVec.ofNat 64 (memW s (globN s "bo" + k))) hm
                  have htoNat : (BitVec.ofNat 64 (memW s (globN s "bo" + k))).toNat
                      = memW s (globN s "bo" + k) :=
                    Nat.mod_eq_of_lt (by have := hhb k hk'; omega)
                  rw [htoNat] at hpos
                  have hexcl : ∀ j, Disj (memW s (globN s "bo" + k), 24) j →
                      ¬ Keccak256.CellHitsPos (memW s (globN s "bo" + k)) j := by
                    intro j hd hc
                    unfold Disj at hd
                    simp only [Keccak256.CellHitsPos, CellHits] at hc
                    rcases hd with hz | hz | hl | hr <;> omega
                  exact hexcl i (hdisjHd i hi) hpos
                have hhd : ∀ k ∈ ([40, 72] : List Nat),
                    memW { post with locals := s.locals } (memW s (globN s "bo" + k)) =
                    memW s (memW s (globN s "bo" + k)) := by
                  intro k hk'
                  have hm := hhdmem k hk'
                  unfold memW at hm ⊢
                  rw [hm]
                exact ptxPhase2X_of_cells hp.1.2
                  (R16Shards.txBacking_of_header_words hp.1.2.2.1 hboG
                    (fun k hk => hcells k (by
                      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
                      rcases hk with rfl | rfl <;> simp)) hhd)
                  rfl hboG hjcG rfl hcells
              -- reassemble the region-E invariant at the restored-locals state
              obtain ⟨S₁, Nd₁, hW₁, hT₁, hd₁, htxte₁, hrec₁⟩ := hp.1.1.1.1.2
              obtain ⟨wte, hwtew⟩ := hp.1.1.1.1.1.2.1
              obtain ⟨wnal, hwnalw⟩ := hp.1.1.1.2.1
              obtain ⟨wnkeys, hwnkeysw⟩ := hp.1.1.2.1
              obtain ⟨walkeys, hwalkeysw⟩ := hp.1.1.2.2.1
              obtain ⟨waladdrs, hwaladdrsw⟩ := hp.1.1.2.2.2.1
              refine ⟨⟨⟨⟨⟨⟨hPVS, ⟨wte, ?_⟩, ?_, ?_, ?_, S₃', Nd₃', hWT₃, ?_⟩,
                S₃', Nd₃', hWT₃, hTAL₃, ?_, ?_, ?_⟩, ⟨wnal, ?_⟩, ?_⟩,
                ⟨wnkeys, ?_⟩, ⟨walkeys, ?_⟩, ⟨waladdrs, ?_⟩,
                ⟨S₃', Nd₃', hWT₃, hTAL₃, ?_, ?_⟩, ?_⟩, hXpost⟩, w, hwl⟩
              · exact hwtew
              · exact ⟨hp.1.1.1.1.1.2.2.1.1, hp.1.1.1.1.1.2.2.1.2.trans hhp⟩
              · exact hp.1.1.1.1.1.2.2.2.1
              · exact wordsOK_transfer hGI hGIout hp.1.1.1.1.1.2.2.2.2.1
              · intro i hi j hj
                simp only [List.mem_singleton] at hi
                subst i
                exact hte₃'.2.1 j hj
              · intro i hi j hj
                simp only [List.mem_singleton] at hi
                subst i
                exact hte₃'.2.1 j hj
              · exact htxte₁
              · intro hn
                change Disj (memW post (locN s "tx" + 208), 24 * memW post (locN s "tx" + 216))
                  (locN s "te", 200)
                change 0 < memW post (locN s "tx" + 216) at hn
                rw [hmem216] at hn
                rw [hmem208, hmem216]
                exact hrec₁ hn
              · exact hwnalw
              · rcases hp.1.1.1.2.2 with h0 | hn
                · exact Or.inl h0
                · refine Or.inr ?_
                  change locN s "nal" = memW post (locN s "tx" + 216)
                  rw [hn]
                  exact hmem216.symm
              · exact hwnkeysw
              · exact hwalkeysw
              · exact hwaladdrsw
              · exact hbufout₃
              · intro i hi j hj
                simp only [List.mem_singleton] at hi
                subst i
                exact hte₃'.2.1 j hj
              · exact ⟨hp.1.1.2.2.2.2.2.1, hp.1.1.2.2.2.2.2.2.trans hhp⟩
            · simp at hr
          | _ => simp at hr

/-! ## The whole segment as a bounded program -/

/-- The te-suffix segment (positions 53..69) replayed with the region-E
invariant: pure preservation of `ptxPhase2EInv` across the segment. -/
theorem ptxPhase2E_bound (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (ht : TerminatingProgBoundedOn ptxPhase2EInv tail b) :
    TerminatingProgBoundedOn ptxPhase2EInv (spinePlug 16 (spineAt 53 ptxCode) tail)
      ((K.«tx_is_blob» + 1) + (K.«tx_is_setcode» + 1) + (K.«alloc» + 1) +
        (K.«keccak256» + 1) + b) := by
  have he : spinePlug 16 (spineAt 53 ptxCode) tail =
      .seq (.store (.op .add [.var .local (ofString "te"), .const 96])
        (.var .local (ofString "al_addrs")))
      (.seq (.store (.op .add [.var .local (ofString "te"), .const 104])
        (.op .add [.var .local (ofString "nal"), .const 1]))
      (.seq (.store (.op .add [.var .local (ofString "te"), .const 112])
        (.var .local (ofString "al_keys")))
      (.seq (.store (.op .add [.var .local (ofString "te"), .const 120])
        (.var .local (ofString "nkeys")))
      (.decCall (ofString "isb") .one (ofString "tx_is_blob") [.var .local (ofString "tx")]
      (.seq (.ite (.cmp .notEqual (.var .local (ofString "isb")) (.const 0))
        (.seq (.store (.op .add [.var .local (ofString "te"), .const 128])
          (.load .one (.op .add [.var .local (ofString "tx"), .const 256])))
          (.store (.op .add [.var .local (ofString "te"), .const 136])
            (.load .one (.op .add [.var .local (ofString "tx"), .const 264]))))
        .skip)
      (.decCall (ofString "issc") .one (ofString "tx_is_setcode") [.var .local (ofString "tx")]
      (.seq (.ite (.cmp .notEqual (.var .local (ofString "issc")) (.const 0))
        (.seq (.store (.op .add [.var .local (ofString "te"), .const 144])
          (.load .one (.op .add [.var .local (ofString "tx"), .const 272])))
          (.store (.op .add [.var .local (ofString "te"), .const 152])
            (.load .one (.op .add [.var .local (ofString "tx"), .const 280]))))
        .skip)
      (.seq (.store (.op .add [.var .local (ofString "te"), .const 160]) (.const 1))
      (.seq (.store (.op .add [.var .local (ofString "te"), .const 168])
        (.var .local (ofString "index")))
      (.decCall (ofString "txh") .one (ofString "alloc") [.const 0x20]
      (.seq (.call (some (none, none)) (ofString "keccak256")
        [.rfield 0 (.var .local (ofString "enc")),
         .rfield 1 (.var .local (ofString "enc")),
         .var .local (ofString "txh")])
      (.seq (.store (.op .add [.var .local (ofString "te"), .const 176])
        (.var .local (ofString "txh")))
      (.seq (.store (.op .add [.var .local (ofString "te"), .const 184])
        (.rfield 0 (.var .local (ofString "intrinsic"))))
      (.seq (.store (.op .add [.var .local (ofString "te"), .const 192])
        (.rfield 1 (.var .local (ofString "intrinsic"))))
      (.seq .skip tail))))))))))))))) := by
    simp only [ptxCode, sourceFunctionEntry, Guest.Software.guestFn_process_transaction, spineAt,
      spinePlug]
    rfl
  -- stores are clock-neutral under any invariant
  have hs {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (addr src : ExpHOL 64) :
      TerminatingProgBoundedOn P (.store addr src) 0 := by
    intro F s hc hp hn
    rw [clock_store]
    exact ⟨by omega, le_rfl⟩
  have hskip : TerminatingProgBoundedOn ptxPhase2EInv .skip 0 := by
    intro F s hc hp hn
    rw [clock_skip]
    exact ⟨by omega, le_rfl⟩
  -- the padding skip before the tail
  have hsk : TerminatingProgBoundedOn ptxPhase2EInv (.seq .skip tail) (0 + b) :=
    seq_bound_trans hskip (Hoare.skip (fun _ hp _ => hp)) ht
  -- the last three te stores
  have h67 : TerminatingProgBoundedOn ptxPhase2EInv
      (.seq (.store (.op .add [.var .local (ofString "te"), .const 192])
          (.rfield 1 (.var .local (ofString "intrinsic"))))
        (.seq .skip tail))
      (0 + (0 + b)) :=
    seq_bound_trans (hs _ _) ptxPhase2E_store_intrinsic_one hsk
  have h66 : TerminatingProgBoundedOn ptxPhase2ETxh
      (.seq (.store (.op .add [.var .local (ofString "te"), .const 184])
          (.rfield 0 (.var .local (ofString "intrinsic"))))
        (.seq (.store (.op .add [.var .local (ofString "te"), .const 192])
            (.rfield 1 (.var .local (ofString "intrinsic"))))
          (.seq .skip tail)))
      (0 + (0 + (0 + b))) :=
    seq_bound_trans (hs _ _)
      (Hoare.mono (P := ptxPhase2ETxh) ptxPhase2E_store_intrinsic_zero
        (fun _ hp => And.left hp)) h67
  have h65 : TerminatingProgBoundedOn ptxPhase2ETxh
      (.seq (.store (.op .add [.var .local (ofString "te"), .const 176])
          (.var .local (ofString "txh")))
        (.seq (.store (.op .add [.var .local (ofString "te"), .const 184])
            (.rfield 0 (.var .local (ofString "intrinsic"))))
          (.seq (.store (.op .add [.var .local (ofString "te"), .const 192])
              (.rfield 1 (.var .local (ofString "intrinsic"))))
            (.seq .skip tail))))
      (0 + (0 + (0 + (0 + b)))) :=
    seq_bound_trans (hs _ _) ptxPhase2E_store_txh h66
  -- the keccak256 hash call
  have hcall : TerminatingProgBoundedOn ptxPhase2EHashReady
      (.seq (.call (some (none, none)) (ofString "keccak256")
          [.rfield 0 (.var .local (ofString "enc")),
           .rfield 1 (.var .local (ofString "enc")),
           .var .local (ofString "txh")])
        (.seq (.store (.op .add [.var .local (ofString "te"), .const 176])
            (.var .local (ofString "txh")))
          (.seq (.store (.op .add [.var .local (ofString "te"), .const 184])
              (.rfield 0 (.var .local (ofString "intrinsic"))))
            (.seq (.store (.op .add [.var .local (ofString "te"), .const 192])
                (.rfield 1 (.var .local (ofString "intrinsic"))))
              (.seq .skip tail)))))
      ((K.«keccak256» + 1) + (0 + (0 + (0 + (0 + b))))) :=
    seq_bound_trans
      (TerminatingProgBoundedOn.call_on h.fb_keccak256 none
        [.rfield 0 (.var .local (ofString "enc")),
         .rfield 1 (.var .local (ofString "enc")),
         .var .local (ofString "txh")]
        (ptxPhase2EHash_callEntry
          [.rfield 0 (.var .local (ofString "enc")),
           .rfield 1 (.var .local (ofString "enc")),
           .var .local (ofString "txh")]))
      (ptxPhase2E_keccak_txh h) h65
  -- the hash-buffer allocation
  have htxh : TerminatingProgBoundedOn ptxPhase2EInv
      (.decCall (ofString "txh") .one (ofString "alloc") [.const 0x20]
        (.seq (.call (some (none, none)) (ofString "keccak256")
            [.rfield 0 (.var .local (ofString "enc")),
             .rfield 1 (.var .local (ofString "enc")),
             .var .local (ofString "txh")])
          (.seq (.store (.op .add [.var .local (ofString "te"), .const 176])
              (.var .local (ofString "txh")))
            (.seq (.store (.op .add [.var .local (ofString "te"), .const 184])
                (.rfield 0 (.var .local (ofString "intrinsic"))))
              (.seq (.store (.op .add [.var .local (ofString "te"), .const 192])
                  (.rfield 1 (.var .local (ofString "intrinsic"))))
                (.seq .skip tail))))))
      (K.«alloc» + ((K.«keccak256» + 1) + (0 + (0 + (0 + (0 + b))))) + 1) :=
    TerminatingProgBoundedOn.decCall_on h.fb_alloc (ofString "txh") .one [.const 0x20]
      (ptxPhase2E_callEntry [.const 0x20]) (ptxPhase2E_alloc_txh h) hcall
  -- the index and one stores
  have hsa : TerminatingProgBoundedOn ptxPhase2EInv
      (.seq (.store (.op .add [.var .local (ofString "te"), .const 168])
          (.var .local (ofString "index")))
        (.decCall (ofString "txh") .one (ofString "alloc") [.const 0x20]
          (.seq (.call (some (none, none)) (ofString "keccak256")
              [.rfield 0 (.var .local (ofString "enc")),
               .rfield 1 (.var .local (ofString "enc")),
               .var .local (ofString "txh")])
            (.seq (.store (.op .add [.var .local (ofString "te"), .const 176])
                (.var .local (ofString "txh")))
              (.seq (.store (.op .add [.var .local (ofString "te"), .const 184])
                  (.rfield 0 (.var .local (ofString "intrinsic"))))
                (.seq (.store (.op .add [.var .local (ofString "te"), .const 192])
                    (.rfield 1 (.var .local (ofString "intrinsic"))))
                  (.seq .skip tail)))))))
      (0 + (K.«alloc» + ((K.«keccak256» + 1) + (0 + (0 + (0 + (0 + b))))) + 1)) :=
    seq_bound_trans (hs _ _) ptxPhase2E_store_index htxh
  have hsb : TerminatingProgBoundedOn ptxPhase2EInv
      (.seq (.store (.op .add [.var .local (ofString "te"), .const 160]) (.const 1))
        (.seq (.store (.op .add [.var .local (ofString "te"), .const 168])
            (.var .local (ofString "index")))
          (.decCall (ofString "txh") .one (ofString "alloc") [.const 0x20]
            (.seq (.call (some (none, none)) (ofString "keccak256")
                [.rfield 0 (.var .local (ofString "enc")),
                 .rfield 1 (.var .local (ofString "enc")),
                 .var .local (ofString "txh")])
              (.seq (.store (.op .add [.var .local (ofString "te"), .const 176])
                  (.var .local (ofString "txh")))
                (.seq (.store (.op .add [.var .local (ofString "te"), .const 184])
                    (.rfield 0 (.var .local (ofString "intrinsic"))))
                  (.seq (.store (.op .add [.var .local (ofString "te"), .const 192])
                      (.rfield 1 (.var .local (ofString "intrinsic"))))
                    (.seq .skip tail))))))))
      (0 + (0 + (K.«alloc» + ((K.«keccak256» + 1) + (0 + (0 + (0 + (0 + b))))) + 1))) :=
    seq_bound_trans (hs _ _) ptxPhase2E_store_const_one hsa
  -- the setcode conditional stores
  have hite2 : TerminatingProgBoundedOn ptxPhase2EInv
      (.ite (.cmp .notEqual (.var .local (ofString "issc")) (.const 0))
        (.seq (.store (.op .add [.var .local (ofString "te"), .const 144])
            (.load .one (.op .add [.var .local (ofString "tx"), .const 272])))
          (.store (.op .add [.var .local (ofString "te"), .const 152])
            (.load .one (.op .add [.var .local (ofString "tx"), .const 280]))))
        .skip) _ :=
    TerminatingProgBoundedOn.ite_on
      (seq_bound_trans (hs _ _) (ptxPhase2E_store_load_one 144 272 18 (by decide) (by omega)
        (by dsimp; omega))
        (hs _ _)) hskip
  -- the setcode flag probe
  have hissc : TerminatingProgBoundedOn ptxPhase2EInv
      (.decCall (ofString "issc") .one (ofString "tx_is_setcode") [.var .local (ofString "tx")]
        (.seq (.ite (.cmp .notEqual (.var .local (ofString "issc")) (.const 0))
            (.seq (.store (.op .add [.var .local (ofString "te"), .const 144])
                (.load .one (.op .add [.var .local (ofString "tx"), .const 272])))
              (.store (.op .add [.var .local (ofString "te"), .const 152])
                (.load .one (.op .add [.var .local (ofString "tx"), .const 280]))))
            .skip)
          (.seq (.store (.op .add [.var .local (ofString "te"), .const 160]) (.const 1))
            (.seq (.store (.op .add [.var .local (ofString "te"), .const 168])
                (.var .local (ofString "index")))
              (.decCall (ofString "txh") .one (ofString "alloc") [.const 0x20]
                (.seq (.call (some (none, none)) (ofString "keccak256")
                    [.rfield 0 (.var .local (ofString "enc")),
                     .rfield 1 (.var .local (ofString "enc")),
                     .var .local (ofString "txh")])
                  (.seq (.store (.op .add [.var .local (ofString "te"), .const 176])
                      (.var .local (ofString "txh")))
                    (.seq (.store (.op .add [.var .local (ofString "te"), .const 184])
                        (.rfield 0 (.var .local (ofString "intrinsic"))))
                      (.seq (.store (.op .add [.var .local (ofString "te"), .const 192])
                          (.rfield 1 (.var .local (ofString "intrinsic"))))
                        (.seq .skip tail)))))))))) _ :=
    TerminatingProgBoundedOn.decCall_on h.fb_tx_is_setcode (ofString "issc") .one
      [.var .local (ofString "tx")] (ptxPhase2E_callEntry [.var .local (ofString "tx")])
      (ptxPhase2E_issc_resume h)
      (seq_bound_trans hite2 ptxPhase2E_setcode_ite hsb)
  -- the blob conditional stores
  have hite1 : TerminatingProgBoundedOn ptxPhase2EInv
      (.ite (.cmp .notEqual (.var .local (ofString "isb")) (.const 0))
        (.seq (.store (.op .add [.var .local (ofString "te"), .const 128])
            (.load .one (.op .add [.var .local (ofString "tx"), .const 256])))
          (.store (.op .add [.var .local (ofString "te"), .const 136])
            (.load .one (.op .add [.var .local (ofString "tx"), .const 264]))))
        .skip) _ :=
    TerminatingProgBoundedOn.ite_on
      (seq_bound_trans (hs _ _) (ptxPhase2E_store_load_one 128 256 16 (by decide) (by omega)
        (by dsimp; omega))
        (hs _ _)) hskip
  -- the blob flag probe
  have hisb : TerminatingProgBoundedOn ptxPhase2EInv
      (.decCall (ofString "isb") .one (ofString "tx_is_blob") [.var .local (ofString "tx")]
        (.seq (.ite (.cmp .notEqual (.var .local (ofString "isb")) (.const 0))
            (.seq (.store (.op .add [.var .local (ofString "te"), .const 128])
                (.load .one (.op .add [.var .local (ofString "tx"), .const 256])))
              (.store (.op .add [.var .local (ofString "te"), .const 136])
                (.load .one (.op .add [.var .local (ofString "tx"), .const 264]))))
            .skip)
          (.decCall (ofString "issc") .one (ofString "tx_is_setcode")
              [.var .local (ofString "tx")]
            (.seq (.ite (.cmp .notEqual (.var .local (ofString "issc")) (.const 0))
                (.seq (.store (.op .add [.var .local (ofString "te"), .const 144])
                    (.load .one (.op .add [.var .local (ofString "tx"), .const 272])))
                  (.store (.op .add [.var .local (ofString "te"), .const 152])
                    (.load .one (.op .add [.var .local (ofString "tx"), .const 280]))))
                .skip)
              (.seq (.store (.op .add [.var .local (ofString "te"), .const 160]) (.const 1))
                (.seq (.store (.op .add [.var .local (ofString "te"), .const 168])
                    (.var .local (ofString "index")))
                  (.decCall (ofString "txh") .one (ofString "alloc") [.const 0x20]
                    (.seq (.call (some (none, none)) (ofString "keccak256")
                        [.rfield 0 (.var .local (ofString "enc")),
                         .rfield 1 (.var .local (ofString "enc")),
                         .var .local (ofString "txh")])
                      (.seq (.store (.op .add [.var .local (ofString "te"), .const 176])
                          (.var .local (ofString "txh")))
                        (.seq (.store (.op .add [.var .local (ofString "te"), .const 184])
                            (.rfield 0 (.var .local (ofString "intrinsic"))))
                          (.seq (.store (.op .add [.var .local (ofString "te"), .const 192])
                              (.rfield 1 (.var .local (ofString "intrinsic"))))
                            (.seq .skip tail)))))))))))) _ :=
    TerminatingProgBoundedOn.decCall_on h.fb_tx_is_blob (ofString "isb") .one
      [.var .local (ofString "tx")] (ptxPhase2E_callEntry [.var .local (ofString "tx")])
      (ptxPhase2E_isb_resume h)
      (seq_bound_trans hite1 ptxPhase2E_blob_ite hissc)
  -- the four access-list stores
  have hmain : TerminatingProgBoundedOn ptxPhase2EInv (spinePlug 16 (spineAt 53 ptxCode) tail)
      (0 + (0 + (0 + (0 +
        (K.«tx_is_blob» + (Nat.max (0 + 0) 0 +
          (K.«tx_is_setcode» + (Nat.max (0 + 0) 0 +
            (0 + (0 + (K.«alloc» + ((K.«keccak256» + 1) +
              (0 + (0 + (0 + (0 + b))))) + 1)))) + 1)) + 1))))) := by
    rw [he]
    exact seq_bound_trans (hs _ _) ptxPhase2E_store_al_addrs
      (seq_bound_trans (hs _ _) ptxPhase2E_store_nal_succ
      (seq_bound_trans (hs _ _) ptxPhase2E_store_al_keys
      (seq_bound_trans (hs _ _) ptxPhase2E_store_nkeys hisb)))
  intro F s hc hp hnt
  obtain ⟨h1, h2⟩ := hmain s hc hp hnt
  have hd : Nat.max (0 + 0) 0 = 0 := by rfl
  rw [hd] at h1
  exact ⟨by omega, h2⟩

end InitECandidate.Solver.Wave8GuestInv.R13Shards
