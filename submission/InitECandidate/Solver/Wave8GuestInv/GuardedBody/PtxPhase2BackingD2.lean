import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase2BackingD

/-!
# Phase 2 backing replay, region D packing loop (guest spine 50..52)

This file threads the region-D strengthened conjuncts (count readiness, the
retained-buffer family, and the scalar witnesses) through the packing loop
that region B only carried with the auxiliary conjunct. The loop structure
mirrors `PtxPhase2BackingB` (inner `j` loop, record increment, declarations,
outer `i` loop), with the three extra conjuncts transferred at every step:
the two `memcpy` calls go through `ptxPhase2D_full_copy` and
`ptxPhase2D_acr_copy`, the counter and declaration steps through the
locals/clock transfer lemmas below. The file closes with the region-D loop
hoare and the guest-position-53 conversion into `ptxPhase2CRInv`.
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

/-! ## Transfer lemmas for the strengthened conjuncts -/

/-- Count readiness survives a clock decrement. -/
theorem ptxPhase2D_acr_decClock {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxAccessCountReady s) : PtxAccessCountReady (decClockHOLFinite s) :=
  phase2_accessCountReady_with_locals s s.locals (s.clock - 1) (by intros; rfl) hp

/-- None of the packing scratch locals is read by the count-ready conjunct. -/
theorem ptxPhase2D_acrNames_ne (name : MlS)
    (hne : name = ofString "k" ∨ name = ofString "j" ∨ name = ofString "i" ∨
      name = ofString "acc2" ∨ name = ofString "ns") :
    ∀ n ∈ (["nal", "te", "tx", "index", "sender", "mgas", "reservoir", "gas",
      "tx_blob_gas_used", "price", "enc", "intrinsic"] : List String),
      ofString n ≠ name := by
  intro n hn h'
  simp at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hne with rfl | rfl | rfl | rfl | rfl <;> exact absurd h' (by decide)

/-- Count readiness survives a packing scratch assignment. -/
theorem ptxPhase2D_acr_setVar_scratch {F : Type} (s : PanSemStateFiniteExact 64 F)
    (v : ValueHOL 64) (name : MlS)
    (hne : name = ofString "k" ∨ name = ofString "j" ∨ name = ofString "i" ∨
      name = ofString "acc2" ∨ name = ofString "ns")
    (hp : PtxAccessCountReady s) :
    PtxAccessCountReady (setVarHOLFinite name v s) := by
  refine phase2_accessCountReady_with_locals s (s.locals.update (name, v)) s.clock ?_ hp
  intro n hn
  simp [HolFiniteMapExact.update, FUPDATE,
    show name ≠ ofString n from ((ptxPhase2D_acrNames_ne name hne) n hn).symm]

/-- None of the packing scratch locals is read by the family or scalar
conjuncts. -/
theorem ptxPhase2D_scratch_ne (name : MlS)
    (hne : name = ofString "k" ∨ name = ofString "j" ∨ name = ofString "i" ∨
      name = ofString "acc2" ∨ name = ofString "ns") :
    (∀ n ∈ ptxPhase2DNames, ofString n ≠ name) ∧ ofString "al_keys" ≠ name := by
  refine ⟨fun n hn h' => ?_, fun h' => ?_⟩
  · simp [ptxPhase2DNames] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl <;>
      rcases hne with rfl | rfl | rfl | rfl | rfl <;> exact absurd h' (by decide)
  · rcases hne with rfl | rfl | rfl | rfl | rfl <;> exact absurd h' (by decide)

/-- The scalar conjunct only reads the locals map. -/
theorem ptxPhase2DScal_locals_only {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (h : t.locals = s.locals) (hp : ptxPhase2DScal s) : ptxPhase2DScal t := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨w, hw⟩ := h1
    exact ⟨w, by rw [h]; exact hw⟩
  · obtain ⟨w, hw⟩ := h2
    exact ⟨w, by rw [h]; exact hw⟩
  · obtain ⟨w, hw⟩ := h3
    exact ⟨w, by rw [h]; exact hw⟩
  · obtain ⟨w, hw⟩ := h4
    exact ⟨w, by rw [h]; exact hw⟩
  · have hte : locN t "te" = locN s "te" := by
      unfold locN
      rw [h]
    rw [hte]
    exact h5

/-! ## The two packing copies under the strengthened conjuncts -/

/-- The first packing copy preserves count readiness, the retained family,
and the scalar witnesses. -/
theorem ptxPhase2D_rich_address_copy_hoare (h : PtxCallees) {contents : Nat → BitVec 64}
    {E T A N : Nat} (src : ExpHOL 64) :
    Hoare (fun s => ptxPhase2BX s ∧ PtxPackedNsNalCopy s ∧ PtxAccessCountReady s ∧
        ptxPhase2DFullR contents E T A N s ∧ ptxPhase2DScal s)
      (.call (some (none, none)) (ofString "memcpy")
        [.op .add [.var .local (ofString "al_keys"),
          .panop .mul [.var .local (ofString "k"), .const 52]], src, .const 20])
      (fun r t => r = none → PtxAccessCountReady t ∧
        ptxPhase2DFullR contents E T A N t ∧ ptxPhase2DScal t) := by
  refine ⟨fun {F} s hc hp hnt hr => ?_⟩
  have hnt0 := hnt
  have hs : PtxPackedNsCopy s := hp.2.1.1
  have hAR : ArenaReady s := hs.1.1.1
  have hG : GuestInv s := hAR.1
  have hci : PtxPackedCopyIndex s := hs.1.2.1.1
  obtain ⟨base, hbase⟩ := hs.1.2.1.1.1.1
  obtain ⟨kk, hkk⟩ := hs.1.2.2.1
  have hbound := hs.1.2.2.2
  have hdst := (phase2_packed_copy_index_destinations hci).1
  have hdsteq : (base + kk * 52).toNat = locN s "al_keys" + 52 * locN s "k" :=
    phase2_packed_destination_toNat s hci base kk hbase hkk hbound
  have hd : evalAt s (.op .add [.var .local (ofString "al_keys"),
      .panop .mul [.var .local (ofString "k"), .const 52]]) =
      some (.val (.word (base + kk * 52))) :=
    phase2_packed_destination_eval s base kk hbase hkk
  have hlen : evalAt s (.const 20) = some (.val (.word (20 : BitVec 64))) := by
    simp [evalAt, evalHOLExact]
  rw [evaluateHOLFiniteState_call] at hr
  rcases ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.op .add [.var .local (ofString "al_keys"),
        .panop .mul [.var .local (ofString "k"), .const 52]], src, .const 20] with _ | vs
  · rw [ha] at hr; simp at hr
  · simp only [ha] at hr
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "memcpy") vs with
      _ | ⟨body, callee, ret⟩
    · simp [hl] at hr
    · simp only [hl] at hr
      by_cases hz : s.clock = 0
      · simp [hz] at hr
      · simp only [hz, ↓reduceIte] at hr
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with
          ⟨res, post⟩
        simp only [hb] at hr
        cases res with
        | none => simp at hr
        | some r =>
          cases r with
          | returned v =>
            dsimp only at hr
            split at hr
            · rename_i hsh
              have hpost_eq : (evaluateHOLFiniteState s
                  (.call (some (none, none)) (ofString "memcpy")
                    [.op .add [.var .local (ofString "al_keys"),
                      .panop .mul [.var .local (ofString "k"), .const 52]], src, .const 20])).2 =
                  {post with locals := s.locals} := by
                rw [evaluateHOLFiniteState_call]
                simp only [ha]
                simp only [hl]
                simp only [hz, ↓reduceIte]
                rw [hb]; dsimp only; rw [if_pos hsh]
              have hor : (evaluateHOLFiniteState s
                  (.call (some (none, none)) (ofString "memcpy")
                    [.op .add [.var .local (ofString "al_keys"),
                      .panop .mul [.var .local (ofString "k"), .const 52]], src, .const 20])).1 = none ∨
                  Resumes (evaluateHOLFiniteState s
                    (.call (some (none, none)) (ofString "memcpy")
                      [.op .add [.var .local (ofString "al_keys"),
                        .panop .mul [.var .local (ofString "k"), .const 52]], src, .const 20])).1 := by
                rw [evaluateHOLFiniteState_call]
                simp only [ha]
                simp only [hl]
                simp only [hz, ↓reduceIte]
                rw [hb]; dsimp only; rw [if_pos hsh]
                exact Or.inl rfl
              obtain ⟨v1, v2, v3, hvs, hv1, hv2, hv3⟩ := ptxPhase2B_evalList_three s ha
              subst hvs
              have hv1' : v1 = .val (.word (base + kk * 52)) :=
                Option.some.inj (by rw [← hv1]; exact hd)
              subst hv1'
              have hv3' : v3 = .val (.word (20 : BitVec 64)) :=
                Option.some.inj (by rw [← hv3]; exact hlen)
              subst hv3'
              have hbe := R13Shards.Keccak256.call0_byteEff
                  R13Shards.Keccak256.funByteEff_memcpy s
                  [.op .add [.var .local (ofString "al_keys"),
                    .panop .mul [.var .local (ofString "k"), .const 52]], src, .const 20]
                  [((base + kk * 52).toNat, 20)] hc hG
                  (fun vals hvs' i hi _ => by
                    rw [ha] at hvs'
                    injection hvs' with hvs'
                    subst hvs'
                    exact ⟨i, hi, Nat.le_refl _, Nat.le_refl _⟩)
                  hnt0 hor
              rw [hpost_eq] at hbe
              have hfull : ptxPhase2DFullR contents E T A N {post with locals := s.locals} :=
                ptxPhase2D_full_copy h s post
                  (.op .add [.var .local (ofString "al_keys"),
                    .panop .mul [.var .local (ofString "k"), .const 52]]) src (.const 20)
                  [.val (.word (base + kk * 52)), v2, .val (.word (20 : BitVec 64))]
                  body callee ret (some (.returned v)) (base + kk * 52) (20 : BitVec 64)
                  hc ha hl hb (by simp) (Or.inl ⟨v, rfl⟩) hp.2.1 hAR hp.2.2.2.1 hd hlen
                  (by rw [hdsteq]; simp)
              have hacr : PtxAccessCountReady {post with locals := s.locals} :=
                ptxPhase2D_acr_copy hp.1 hp.2.1 hp.2.2.1 hc rfl hbe hfull
                  (by rw [hdsteq]; exact hdst)
              rw [hpost_eq]
              exact ⟨hacr, hfull, ptxPhase2DScal_locals_only rfl hp.2.2.2.2⟩
            · simp at hr
          | _ => simp at hr

/-- The second packing copy preserves count readiness, the retained family,
and the scalar witnesses. -/
theorem ptxPhase2D_rich_storage_copy_hoare (h : PtxCallees) {contents : Nat → BitVec 64}
    {E T A N : Nat} (src : ExpHOL 64) :
    Hoare (fun s => ptxPhase2BX s ∧ PtxPackedNsNalCopy s ∧ PtxAccessCountReady s ∧
        ptxPhase2DFullR contents E T A N s ∧ ptxPhase2DScal s)
      (.call (some (none, none)) (ofString "memcpy")
        [.op .add [.var .local (ofString "al_keys"),
          .panop .mul [.var .local (ofString "k"), .const 52], .const 20], src, .const 32])
      (fun r t => r = none → PtxAccessCountReady t ∧
        ptxPhase2DFullR contents E T A N t ∧ ptxPhase2DScal t) := by
  refine ⟨fun {F} s hc hp hnt hr => ?_⟩
  have hnt0 := hnt
  have hs : PtxPackedNsCopy s := hp.2.1.1
  have hAR : ArenaReady s := hs.1.1.1
  have hG : GuestInv s := hAR.1
  have hci : PtxPackedCopyIndex s := hs.1.2.1.1
  obtain ⟨base, hbase⟩ := hs.1.2.1.1.1.1
  obtain ⟨kk, hkk⟩ := hs.1.2.2.1
  have hbound := hs.1.2.2.2
  have hdst := (phase2_packed_copy_index_destinations hci).2
  have hdsteq : (base + kk * 52 + 20).toNat = locN s "al_keys" + 52 * locN s "k" + 20 :=
    phase2_packed_key_destination_toNat s hci base kk hbase hkk hbound
  have hd : evalAt s (.op .add [.var .local (ofString "al_keys"),
      .panop .mul [.var .local (ofString "k"), .const 52], .const 20]) =
      some (.val (.word (base + kk * 52 + 20))) :=
    phase2_packed_key_destination_eval s base kk hbase hkk
  have hlen : evalAt s (.const 32) = some (.val (.word (32 : BitVec 64))) := by
    simp [evalAt, evalHOLExact]
  rw [evaluateHOLFiniteState_call] at hr
  rcases ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.op .add [.var .local (ofString "al_keys"),
        .panop .mul [.var .local (ofString "k"), .const 52], .const 20], src, .const 32] with _ | vs
  · rw [ha] at hr; simp at hr
  · simp only [ha] at hr
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "memcpy") vs with
      _ | ⟨body, callee, ret⟩
    · simp [hl] at hr
    · simp only [hl] at hr
      by_cases hz : s.clock = 0
      · simp [hz] at hr
      · simp only [hz, ↓reduceIte] at hr
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with
          ⟨res, post⟩
        simp only [hb] at hr
        cases res with
        | none => simp at hr
        | some r =>
          cases r with
          | returned v =>
            dsimp only at hr
            split at hr
            · rename_i hsh
              have hpost_eq : (evaluateHOLFiniteState s
                  (.call (some (none, none)) (ofString "memcpy")
                    [.op .add [.var .local (ofString "al_keys"),
                      .panop .mul [.var .local (ofString "k"), .const 52], .const 20],
                      src, .const 32])).2 =
                  {post with locals := s.locals} := by
                rw [evaluateHOLFiniteState_call]
                simp only [ha]
                simp only [hl]
                simp only [hz, ↓reduceIte]
                rw [hb]; dsimp only; rw [if_pos hsh]
              have hor : (evaluateHOLFiniteState s
                  (.call (some (none, none)) (ofString "memcpy")
                    [.op .add [.var .local (ofString "al_keys"),
                      .panop .mul [.var .local (ofString "k"), .const 52], .const 20],
                      src, .const 32])).1 = none ∨
                  Resumes (evaluateHOLFiniteState s
                    (.call (some (none, none)) (ofString "memcpy")
                      [.op .add [.var .local (ofString "al_keys"),
                        .panop .mul [.var .local (ofString "k"), .const 52], .const 20],
                        src, .const 32])).1 := by
                rw [evaluateHOLFiniteState_call]
                simp only [ha]
                simp only [hl]
                simp only [hz, ↓reduceIte]
                rw [hb]; dsimp only; rw [if_pos hsh]
                exact Or.inl rfl
              obtain ⟨v1, v2, v3, hvs, hv1, hv2, hv3⟩ := ptxPhase2B_evalList_three s ha
              subst hvs
              have hv1' : v1 = .val (.word (base + kk * 52 + 20)) :=
                Option.some.inj (by rw [← hv1]; exact hd)
              subst hv1'
              have hv3' : v3 = .val (.word (32 : BitVec 64)) :=
                Option.some.inj (by rw [← hv3]; exact hlen)
              subst hv3'
              have hbe := R13Shards.Keccak256.call0_byteEff
                  R13Shards.Keccak256.funByteEff_memcpy s
                  [.op .add [.var .local (ofString "al_keys"),
                    .panop .mul [.var .local (ofString "k"), .const 52], .const 20],
                    src, .const 32]
                  [((base + kk * 52 + 20).toNat, 32)] hc hG
                  (fun vals hvs' i hi _ => by
                    rw [ha] at hvs'
                    injection hvs' with hvs'
                    subst hvs'
                    exact ⟨i, hi, Nat.le_refl _, Nat.le_refl _⟩)
                  hnt0 hor
              rw [hpost_eq] at hbe
              have hfull : ptxPhase2DFullR contents E T A N {post with locals := s.locals} :=
                ptxPhase2D_full_copy h s post
                  (.op .add [.var .local (ofString "al_keys"),
                    .panop .mul [.var .local (ofString "k"), .const 52], .const 20])
                  src (.const 32)
                  [.val (.word (base + kk * 52 + 20)), v2, .val (.word (32 : BitVec 64))]
                  body callee ret (some (.returned v)) (base + kk * 52 + 20) (32 : BitVec 64)
                  hc ha hl hb (by simp) (Or.inl ⟨v, rfl⟩) hp.2.1 hAR hp.2.2.2.1 hd hlen
                  (by rw [hdsteq]; simp)
              have hacr : PtxAccessCountReady {post with locals := s.locals} :=
                ptxPhase2D_acr_copy hp.1 hp.2.1 hp.2.2.1 hc rfl hbe hfull
                  (by rw [hdsteq]; exact hdst)
              rw [hpost_eq]
              exact ⟨hacr, hfull, ptxPhase2DScal_locals_only rfl hp.2.2.2.2⟩
            · simp at hr
          | _ => simp at hr

/-- The first packing copy under the full loop invariant. -/
theorem ptxPhase2D_address_copy_hoare (h : PtxCallees) {contents : Nat → BitVec 64}
    {E T A N : Nat} (src : ExpHOL 64) :
    Hoare (fun s => ptxPhase2BX s ∧ PtxPackedNsNalCopy s ∧ PtxAccessCountReady s ∧
        ptxPhase2DFullR contents E T A N s ∧ ptxPhase2DScal s)
      (.call (some (none, none)) (ofString "memcpy")
        [.op .add [.var .local (ofString "al_keys"),
          .panop .mul [.var .local (ofString "k"), .const 52]], src, .const 20])
      (fun r t => r = none → ptxPhase2BX t ∧ PtxPackedNsNalCopy t ∧
        PtxAccessCountReady t ∧ ptxPhase2DFullR contents E T A N t ∧ ptxPhase2DScal t) := by
  have hb : Hoare (fun s => ptxPhase2BX s ∧ PtxPackedNsNalCopy s)
      (.call (some (none, none)) (ofString "memcpy")
        [.op .add [.var .local (ofString "al_keys"),
          .panop .mul [.var .local (ofString "k"), .const 52]], src, .const 20])
      (fun r t => r = none → ptxPhase2BX t ∧ PtxPackedNsNalCopy t) :=
    ptxPhase2BX_packed_address_copy_hoare h src
  have hr : Hoare (fun s => ptxPhase2BX s ∧ PtxPackedNsNalCopy s ∧ PtxAccessCountReady s ∧
        ptxPhase2DFullR contents E T A N s ∧ ptxPhase2DScal s)
      (.call (some (none, none)) (ofString "memcpy")
        [.op .add [.var .local (ofString "al_keys"),
          .panop .mul [.var .local (ofString "k"), .const 52]], src, .const 20])
      (fun r t => r = none → PtxAccessCountReady t ∧
        ptxPhase2DFullR contents E T A N t ∧ ptxPhase2DScal t) :=
    ptxPhase2D_rich_address_copy_hoare h src
  exact ptxPhase2B_hoare_post
    (ptxPhase2B_hoare_pair (Hoare.mono (P := fun s => ptxPhase2BX s ∧ PtxPackedNsNalCopy s ∧
      PtxAccessCountReady s ∧ ptxPhase2DFullR contents E T A N s ∧ ptxPhase2DScal s)
      (P' := fun s => ptxPhase2BX s ∧ PtxPackedNsNalCopy s) hb
      (fun _ hst => ⟨hst.1, hst.2.1⟩)) hr)
    (fun r t hpair hnone => ⟨(hpair.1 hnone).1, (hpair.1 hnone).2,
      (hpair.2 hnone).1, (hpair.2 hnone).2.1, (hpair.2 hnone).2.2⟩)

/-- The second packing copy under the full loop invariant. -/
theorem ptxPhase2D_storage_copy_hoare (h : PtxCallees) {contents : Nat → BitVec 64}
    {E T A N : Nat} (src : ExpHOL 64) :
    Hoare (fun s => ptxPhase2BX s ∧ PtxPackedNsNalCopy s ∧ PtxAccessCountReady s ∧
        ptxPhase2DFullR contents E T A N s ∧ ptxPhase2DScal s)
      (.call (some (none, none)) (ofString "memcpy")
        [.op .add [.var .local (ofString "al_keys"),
          .panop .mul [.var .local (ofString "k"), .const 52], .const 20], src, .const 32])
      (fun r t => r = none → ptxPhase2BX t ∧ PtxPackedNsNalCopy t ∧
        PtxAccessCountReady t ∧ ptxPhase2DFullR contents E T A N t ∧ ptxPhase2DScal t) := by
  have hb : Hoare (fun s => ptxPhase2BX s ∧ PtxPackedNsNalCopy s)
      (.call (some (none, none)) (ofString "memcpy")
        [.op .add [.var .local (ofString "al_keys"),
          .panop .mul [.var .local (ofString "k"), .const 52], .const 20], src, .const 32])
      (fun r t => r = none → ptxPhase2BX t ∧ PtxPackedNsNalCopy t) :=
    ptxPhase2BX_packed_storage_copy_hoare h src
  have hr : Hoare (fun s => ptxPhase2BX s ∧ PtxPackedNsNalCopy s ∧ PtxAccessCountReady s ∧
        ptxPhase2DFullR contents E T A N s ∧ ptxPhase2DScal s)
      (.call (some (none, none)) (ofString "memcpy")
        [.op .add [.var .local (ofString "al_keys"),
          .panop .mul [.var .local (ofString "k"), .const 52], .const 20], src, .const 32])
      (fun r t => r = none → PtxAccessCountReady t ∧
        ptxPhase2DFullR contents E T A N t ∧ ptxPhase2DScal t) :=
    ptxPhase2D_rich_storage_copy_hoare h src
  exact ptxPhase2B_hoare_post
    (ptxPhase2B_hoare_pair (Hoare.mono (P := fun s => ptxPhase2BX s ∧ PtxPackedNsNalCopy s ∧
      PtxAccessCountReady s ∧ ptxPhase2DFullR contents E T A N s ∧ ptxPhase2DScal s)
      (P' := fun s => ptxPhase2BX s ∧ PtxPackedNsNalCopy s) hb
      (fun _ hst => ⟨hst.1, hst.2.1⟩)) hr)
    (fun r t hpair hnone => ⟨(hpair.1 hnone).1, (hpair.1 hnone).2,
      (hpair.2 hnone).1, (hpair.2 hnone).2.1, (hpair.2 hnone).2.2⟩)

/-! ## The counter updates -/

/-- Both counter increments preserve the auxiliary conjunct together with
the strengthened conjuncts. -/
theorem ptxPhase2D_counters_hoare {contents : Nat → BitVec 64} {E T A N : Nat} :
    Hoare (fun s => ptxPhase2BX s ∧ PtxPackedNsNalCopy s ∧ PtxAccessCountReady s ∧
        ptxPhase2DFullR contents E T A N s ∧ ptxPhase2DScal s)
      (.seq
        (.assign .local (ofString "k") (.op .add [.var .local (ofString "k"), .const 1]))
        (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1])))
      (fun r s => r = none → ptxPhase2BX s ∧ PtxPackedNsNalIteration s ∧
        PtxAccessCountReady s ∧ ptxPhase2DFullR contents E T A N s ∧
        ptxPhase2DScal s) := by
  apply Hoare.seq_fall (R := fun s => ∃ before, ptxPhase2BX before ∧
    PtxPackedNsNalCopy before ∧ PtxAccessCountReady before ∧
    ptxPhase2DFullR contents E T A N before ∧ ptxPhase2DScal before ∧
    s = setVarHOLFinite (ofString "k")
      (.val (.word (BitVec.ofNat 64 (locN before "k" + 1)))) before)
  · apply Hoare.assign
    · intro F s v hp he
      have hb := (phase2_packed_copy_counter_bounds hp.2.1.1.1.2.1.1).1
      obtain ⟨w, rfl, hw⟩ := phase2_copy_increment_eval s "k" v hb he
      have heq : w = BitVec.ofNat 64 (locN s "k" + 1) := by
        apply BitVec.eq_of_toNat_eq
        rw [hw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
      subst w
      exact fun _ => ⟨s, hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2, rfl⟩
    · exact fun _ _ hr => by cases hr
  · apply Hoare.assign
    · intro F s v hp he
      obtain ⟨before, hbx, hnc, hacr, hfull, hscal, rfl⟩ := hp
      have hj : locN (setVarHOLFinite (ofString "k")
          (.val (.word (BitVec.ofNat 64 (locN before "k" + 1)))) before) "j" =
          locN before "j" := by
        simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
          show ofString "k" ≠ ofString "j" by decide]
      have hb := (phase2_packed_copy_counter_bounds hnc.1.1.2.1.1).2
      obtain ⟨w, rfl, hw⟩ := phase2_copy_increment_eval _ "j" v (by rw [hj]; exact hb) he
      have heq : w = BitVec.ofNat 64 (locN before "j" + 1) := by
        apply BitVec.eq_of_toNat_eq
        rw [hw, hj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
      subst w
      have hkacr : PtxAccessCountReady (setVarHOLFinite (ofString "k")
          (.val (.word (BitVec.ofNat 64 (locN before "k" + 1)))) before) :=
        ptxPhase2D_acr_setVar_scratch before _ (ofString "k")
          (Or.inl rfl) hacr
      have hkfull : ptxPhase2DFullR contents E T A N (setVarHOLFinite (ofString "k")
          (.val (.word (BitVec.ofNat 64 (locN before "k" + 1)))) before) :=
        ptxPhase2D_fullR_setVar_other before _ (ofString "k")
          ((ptxPhase2D_scratch_ne (ofString "k") (Or.inl rfl)).1)
          ((ptxPhase2D_scratch_ne (ofString "k") (Or.inl rfl)).2) hfull
      have hkscal : ptxPhase2DScal (setVarHOLFinite (ofString "k")
          (.val (.word (BitVec.ofNat 64 (locN before "k" + 1)))) before) :=
        ptxPhase2D_scal_setVar_other before _ (ofString "k")
          ((ptxPhase2D_scratch_ne (ofString "k") (Or.inl rfl)).1) hscal
      refine fun _ => ⟨ptxPhase2BX_setVar_counters before _ _ hbx, ?_,
        ptxPhase2D_acr_setVar_scratch _ _ (ofString "j") (Or.inr (Or.inl rfl)) hkacr,
        ptxPhase2D_fullR_setVar_other _ _ (ofString "j")
          ((ptxPhase2D_scratch_ne (ofString "j") (Or.inr (Or.inl rfl))).1)
          ((ptxPhase2D_scratch_ne (ofString "j") (Or.inr (Or.inl rfl))).2) hkfull,
        ptxPhase2D_scal_setVar_other _ _ (ofString "j")
          ((ptxPhase2D_scratch_ne (ofString "j") (Or.inr (Or.inl rfl))).1) hkscal⟩
      exact ⟨⟨phase2_packed_counters_iteration_state before hnc.1.1.1 hnc.1.1.2.1
          hnc.1.1.2.2.2, phase2_packed_ns_counters before hnc.1 _ _⟩,
        phase2_packed_nal_counters before hnc _ _⟩
    · exact fun _ _ hr => by cases hr

/-- Both copies and both counters preserve the auxiliary conjunct together
with the strengthened conjuncts and the source-loop invariant. -/
theorem ptxPhase2D_body_hoare (h : PtxCallees) {contents : Nat → BitVec 64} {E T A N : Nat}
    (addressSrc keySrc : ExpHOL 64) :
    Hoare (fun s => ptxPhase2BX s ∧ PtxPackedNsNalCopy s ∧ PtxAccessCountReady s ∧
        ptxPhase2DFullR contents E T A N s ∧ ptxPhase2DScal s)
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
      (fun r s => r = none → ptxPhase2BX s ∧ PtxPackedNsNalIteration s ∧
        PtxAccessCountReady s ∧ ptxPhase2DFullR contents E T A N s ∧ ptxPhase2DScal s) :=
  Hoare.seq_fall (ptxPhase2D_address_copy_hoare h addressSrc)
    (Hoare.seq_fall (ptxPhase2D_storage_copy_hoare h keySrc)
      ptxPhase2D_counters_hoare)

/-! ## The inner packing loop under the strengthened conjuncts -/

/-- The cached-count inner loop retains every strengthened conjunct and
finishes with the key-prefix glue. -/
theorem ptxPhase2D_innerWhile_hoare {contents : Nat → BitVec 64} {E T A N : Nat}
    {body : ProgHOL 64}
    (hb : Hoare (fun s => ptxPhase2BX s ∧ PtxPackedNsNalCopy s ∧ PtxAccessCountReady s ∧
        ptxPhase2DFullR contents E T A N s ∧ ptxPhase2DScal s) body
      (fun r s => r = none → ptxPhase2BX s ∧ PtxPackedNsNalIteration s ∧
        PtxAccessCountReady s ∧ ptxPhase2DFullR contents E T A N s ∧ ptxPhase2DScal s))
    (hnb : InitECandidate.Solver.GuestUniformClockBound.noTopBreak body = true)
    (hnc : InitECandidate.Solver.PanRunBounded.noTopContinue body = true) :
    Hoare (fun s => ptxPhase2BX s ∧ PtxPackedNsNalIteration s ∧ PtxAccessCountReady s ∧
        ptxPhase2DFullR contents E T A N s ∧ ptxPhase2DScal s)
      (.while (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "ns"))) body)
      (fun r s => r = none → ptxPhase2BX s ∧ PtxPackedNsNalIteration s ∧
        PtxAccessCountReady s ∧ ptxPhase2DFullR contents E T A N s ∧ ptxPhase2DScal s ∧
        locN s "k" = phase2_key_prefix s (locN s "i" + 1)) := by
  let guard : ExpHOL 64 := .cmp .less (.var .local (ofString "j")) (.var .local (ofString "ns"))
  refine ⟨fun {F} s hc hp _ hr => ?_⟩
  generalize he : evaluateHOLFiniteState s (.while guard body) = out at hr ⊢
  obtain ⟨r, post⟩ := out
  dsimp only at hr
  subst r
  suffices ∀ (k : Nat) (st : PanSemStateFiniteExact 64 F), st.clock = k →
      st.code = originalRuntimeCode → ptxPhase2BX st ∧ PtxPackedNsNalIteration st ∧
        PtxAccessCountReady st ∧ ptxPhase2DFullR contents E T A N st ∧ ptxPhase2DScal st →
      evaluateHOLFiniteState st (.while guard body) = (none, post) →
      ptxPhase2BX post ∧ PtxPackedNsNalIteration post ∧
        PtxAccessCountReady post ∧ ptxPhase2DFullR contents E T A N post ∧
        ptxPhase2DScal post ∧
        locN post "k" = phase2_key_prefix post (locN post "i" + 1) from
    this s.clock s rfl hc hp he
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro st hk hc hp he
    rw [evaluateHOLFiniteState_while_total] at he
    split at he
    · rename_i w hw
      have hguard := phase2_packed_ns_guard_eval st w hp.2.1.1
        (by simpa [evalAt, guard] using hw)
      split at he
      · rename_i hnz
        split at he
        · simp at he
        · dsimp only at he
          rw [fixClockHOLFinite_evaluateState] at he
          have hdBX := ptxPhase2BX_decClock st hp.1
          have hd := phase2_packed_ns_iteration_decClock st hp.2.1.1
          have hdACR := ptxPhase2D_acr_decClock hp.2.2.1
          have hdFullR := ptxPhase2D_fullR_decClock hp.2.2.2.1
          have hdScal := ptxPhase2D_scal_decClock hp.2.2.2.2
          have hm := (InitECandidate.Solver.PanRunBounded.evaluateHOLFiniteState_metadata
            (decClockHOLFinite st) body).1
          have hclk := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) body
          have hbr := InitECandidate.Solver.GuestUniformClockBound.evaluate_noTopBreak body hnb
            (decClockHOLFinite st)
          have hco := InitECandidate.Solver.PanRunBounded.evaluate_noTopContinue body hnc
            (decClockHOLFinite st)
          rcases hrun : evaluateHOLFiniteState (decClockHOLFinite st) body with ⟨r, mid⟩
          rw [hrun] at he hm hclk hbr hco
          cases r with
          | none =>
            have hmid := hb.run (decClockHOLFinite st) hc
              ⟨hdBX, ⟨⟨phase2_packed_iteration_guard_pre _ hd.1 (hguard.mp hnz), hd.2⟩,
                hp.2.1.2⟩, hdACR, hdFullR, hdScal⟩
              (by rw [hrun]; simp) (by rw [hrun])
            rw [hrun] at hmid
            apply ih mid.clock (by change mid.clock ≤ st.clock - 1 at hclk; omega)
              mid rfl (hm.trans hc) hmid he
          | some r => cases r <;> simp_all
      · rename_i hz
        simp at he
        obtain ⟨_, rfl⟩ := he
        exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2,
          (phase2_packed_separated_inner_exit hp.2.1.1.1.2.1
            (fun hlt => hz (hguard.mpr hlt))).1⟩
    · simp at he

/-- The record increment retains the strengthened conjuncts. -/
theorem ptxPhase2D_outerIncrement_hoare {contents : Nat → BitVec 64} {E T A N : Nat} :
    Hoare (fun s => ptxPhase2BX s ∧ PtxPackedNsNalIteration s ∧ PtxAccessCountReady s ∧
        ptxPhase2DFullR contents E T A N s ∧ ptxPhase2DScal s ∧
        locN s "k" = phase2_key_prefix s (locN s "i" + 1))
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))
      (fun r s => r = none → ptxPhase2BX s ∧ PtxPackedNalIteration s ∧
        PtxAccessCountReady s ∧ ptxPhase2DFullR contents E T A N s ∧ ptxPhase2DScal s) := by
  apply Hoare.assign
  · intro F s v hp he
    have hbx := hp.1
    have hiter := hp.2.1
    have hacr := hp.2.2.1
    have hfull := hp.2.2.2.1
    have hscal := hp.2.2.2.2.1
    have hkpre := hp.2.2.2.2.2
    have hb := phase2_packed_outer_successor_bound hiter.1.1.2.1.1
    obtain ⟨w, rfl, hw⟩ := phase2_copy_increment_eval s "i" v hb he
    have heq : w = BitVec.ofNat 64 (locN s "i" + 1) := by
      apply BitVec.eq_of_toNat_eq
      rw [hw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
    subst w
    refine fun _ => ⟨ptxPhase2BX_setVar_other s _ (ofString "i") (by
      intro n hn
      simp [ptxPhase2BXNames, ptxPhase2XNames] at hn
      rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) hbx,
      ⟨⟨phase2_packed_ns_outer_advance s hiter.1 hkpre, ?_⟩, ?_, ?_, ?_⟩⟩
    · simpa [locN, memW, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
        show ofString "i" ≠ ofString "nal" by decide,
        show ofString "i" ≠ ofString "tx" by decide] using hiter.2
    · exact ptxPhase2D_acr_setVar_scratch s _ (ofString "i")
        (Or.inr (Or.inr (Or.inl rfl))) hacr
    · exact ptxPhase2D_fullR_setVar_other s _ (ofString "i")
        ((ptxPhase2D_scratch_ne (ofString "i") (Or.inr (Or.inr (Or.inl rfl)))).1)
        ((ptxPhase2D_scratch_ne (ofString "i") (Or.inr (Or.inr (Or.inl rfl)))).2) hfull
    · exact ptxPhase2D_scal_setVar_other s _ (ofString "i")
        ((ptxPhase2D_scratch_ne (ofString "i") (Or.inr (Or.inr (Or.inl rfl)))).1) hscal
  · exact fun _ _ hr => by cases hr

/-- The concrete inner loop and record increment retain the strengthened
conjuncts together with the outer cached bound. -/
theorem ptxPhase2D_innerTail_hoare (h : PtxCallees) {contents : Nat → BitVec 64} {E T A N : Nat} :
    Hoare (fun s => ptxPhase2BX s ∧ PtxPackedNsNalIteration s ∧ PtxAccessCountReady s ∧
        ptxPhase2DFullR contents E T A N s ∧ ptxPhase2DScal s)
      phase2_packed_source_inner_tail
      (fun r s => r = none → ptxPhase2BX s ∧ PtxPackedNalIteration s ∧
        PtxAccessCountReady s ∧ ptxPhase2DFullR contents E T A N s ∧ ptxPhase2DScal s) := by
  exact Hoare.seq_fall
    (ptxPhase2D_innerWhile_hoare (ptxPhase2D_body_hoare h _ _) rfl rfl)
    ptxPhase2D_outerIncrement_hoare

/-! ### The declaration frame -/

/-- Locals the region-D packing declarations must preserve in their frame. -/
def ptxPhase2DDecNames : List String :=
  ptxPhase2BXNames ++ ["te", "al_addrs", "reservoir", "enc", "i", "k", "nal"]

theorem ptxPhase2BXNames_sub_D2DecNames {n : String} (hn : n ∈ ptxPhase2BXNames) :
    n ∈ ptxPhase2DDecNames := by
  simp only [ptxPhase2DDecNames, List.mem_append]
  exact Or.inl hn

theorem nalNames_sub_D2DecNames {n : String}
    (hn : n ∈ (["al_keys", "nkeys", "tx", "i", "k", "nal"] : List String)) :
    n ∈ ptxPhase2DDecNames := by
  simp at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [ptxPhase2DDecNames, ptxPhase2BXNames, ptxPhase2XNames]

theorem ptxPhase2DACRNames_sub_D2DecNames {n : String}
    (hn : n ∈ (["nal", "te", "tx", "index", "sender", "mgas", "reservoir", "gas",
      "tx_blob_gas_used", "price", "enc", "intrinsic"] : List String)) :
    n ∈ ptxPhase2DDecNames := by
  simp at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [ptxPhase2DDecNames, ptxPhase2BXNames, ptxPhase2XNames]

theorem ptxPhase2DDNames_sub_D2DecNames {n : String} (hn : n ∈ ptxPhase2DNames) :
    n ∈ ptxPhase2DDecNames := by
  simp [ptxPhase2DNames] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl <;>
    simp [ptxPhase2DDecNames, ptxPhase2BXNames, ptxPhase2XNames]

theorem ptxPhase2DDecNames_al_keys :
    ("al_keys" : String) ∈ ptxPhase2DDecNames := by
  simp [ptxPhase2DDecNames, ptxPhase2BXNames]

theorem ptxPhase2DDecNames_ne (name : MlS)
    (hne : name = ofString "acc2" ∨ name = ofString "ns" ∨ name = ofString "j") :
    ∀ n ∈ ptxPhase2DDecNames, ofString n ≠ name := by
  intro n hn h'
  simp [ptxPhase2DDecNames, ptxPhase2BXNames, ptxPhase2XNames] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;>
    rcases hne with rfl | rfl | rfl <;> exact absurd h' (by decide)

/-- The actual nested declarations and copy loop preserve the strengthened
conjuncts together with the source outer-loop invariant. -/
theorem ptxPhase2D_outerBody_hoare (h : PtxCallees) {contents : Nat → BitVec 64} {E T A N : Nat} :
    Hoare (fun s => ptxPhase2BX s ∧ PtxPackedNalIteration s ∧ PtxAccessCountReady s ∧
        ptxPhase2DFullR contents E T A N s ∧ ptxPhase2DScal s ∧
      locN s "i" < memW s (locN s "tx" + 216)) phase2_packed_source_outer_body
      (fun r s => r = none → ptxPhase2BX s ∧ PtxPackedNalIteration s ∧
        PtxAccessCountReady s ∧ ptxPhase2DFullR contents E T A N s ∧ ptxPhase2DScal s) := by
  unfold phase2_packed_source_outer_body
  apply Hoare.dec (names := ptxPhase2DDecNames)
    (P' := fun s => ptxPhase2BX s ∧ PtxPackedNalIteration s ∧ PtxAccessCountReady s ∧
      ptxPhase2DFullR contents E T A N s ∧ ptxPhase2DScal s ∧
      locN s "i" < memW s (locN s "tx" + 216) ∧
      locN s "acc2" = memW s (locN s "tx" + 208) + 24 * locN s "i")
    (ptxPhase2DDecNames_ne (ofString "acc2") (Or.inl rfl))
  · intro F s v hp he
    have hd := phase2_packed_outer_declare_acc2 s hp.2.1.1 hp.2.2.2.2.2 v he
    refine ⟨ptxPhase2BX_setVar_scratch s v (ofString "acc2") hp.1
        (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
      phase2_packed_nal_set_other s hp.2.1 _ _ (by decide), ?_, ?_, ?_, hd.2⟩
    · exact ptxPhase2D_acr_setVar_scratch s v (ofString "acc2")
        (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hp.2.2.1
    · exact ptxPhase2D_fullR_setVar_other s v (ofString "acc2")
        ((ptxPhase2D_scratch_ne (ofString "acc2") (Or.inr (Or.inr (Or.inr (Or.inl rfl))))).1)
        ((ptxPhase2D_scratch_ne (ofString "acc2") (Or.inr (Or.inr (Or.inr (Or.inl rfl))))).2)
        hp.2.2.2.1
    · exact ptxPhase2D_scal_setVar_other s v (ofString "acc2")
        ((ptxPhase2D_scratch_ne (ofString "acc2") (Or.inr (Or.inr (Or.inr (Or.inl rfl))))).1)
        hp.2.2.2.2.1
  · apply Hoare.dec (names := ptxPhase2DDecNames)
      (P' := fun s => ptxPhase2BX s ∧ PtxPackedNalIteration s ∧ PtxAccessCountReady s ∧
        ptxPhase2DFullR contents E T A N s ∧ ptxPhase2DScal s ∧
        locN s "i" < memW s (locN s "tx" + 216) ∧
        (∃ n : BitVec 64, s.locals.lookup (ofString "ns") = some (.val (.word n))) ∧
        locN s "ns" = memW s (memW s (locN s "tx" + 208) + 24 * locN s "i" + 16))
      (ptxPhase2DDecNames_ne (ofString "ns") (Or.inr (Or.inl rfl)))
    · intro F s v hp he
      have hd := phase2_packed_outer_declare_ns s hp.2.1.1 hp.2.2.2.2.2.1 hp.2.2.2.2.2.2 v he
      refine ⟨ptxPhase2BX_setVar_scratch s v (ofString "ns") hp.1
          (Or.inr (Or.inr (Or.inr (Or.inr rfl)))),
        phase2_packed_nal_set_other s hp.2.1 _ _ (by decide), ?_, ?_, ?_, hd.2⟩
      · exact ptxPhase2D_acr_setVar_scratch s v (ofString "ns")
          (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hp.2.2.1
      · exact ptxPhase2D_fullR_setVar_other s v (ofString "ns")
          ((ptxPhase2D_scratch_ne (ofString "ns") (Or.inr (Or.inr (Or.inr (Or.inr rfl))))).1)
          ((ptxPhase2D_scratch_ne (ofString "ns") (Or.inr (Or.inr (Or.inr (Or.inr rfl))))).2)
          hp.2.2.2.1
      · exact ptxPhase2D_scal_setVar_other s v (ofString "ns")
          ((ptxPhase2D_scratch_ne (ofString "ns") (Or.inr (Or.inr (Or.inr (Or.inr rfl))))).1)
          hp.2.2.2.2.1
    · apply Hoare.dec (names := ptxPhase2DDecNames)
        (P' := fun s => ptxPhase2BX s ∧ PtxPackedNsNalIteration s ∧ PtxAccessCountReady s ∧
          ptxPhase2DFullR contents E T A N s ∧ ptxPhase2DScal s)
        (ptxPhase2DDecNames_ne (ofString "j") (Or.inr (Or.inr rfl)))
      · intro F s v hp he
        have hv : v = .val (.word 0) := by simpa [evalAt, evalHOLExact] using he.symm
        subst v
        refine ⟨ptxPhase2BX_setVar_scratch s (.val (.word 0)) (ofString "j") hp.1
            (Or.inr (Or.inl rfl)), ⟨⟨phase2_packed_ns_reset s hp.2.1.1 hp.2.2.2.2.2.1
            hp.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2, ?_⟩, ?_, ?_, ?_⟩⟩
        · exact (phase2_packed_nal_set_other s hp.2.1 (ofString "j") (.val (.word 0))
            (by decide)).2
        · exact ptxPhase2D_acr_setVar_scratch s (.val (.word 0)) (ofString "j")
            (Or.inr (Or.inl rfl)) hp.2.2.1
        · exact ptxPhase2D_fullR_setVar_other s (.val (.word 0)) (ofString "j")
            ((ptxPhase2D_scratch_ne (ofString "j") (Or.inr (Or.inl rfl))).1)
            ((ptxPhase2D_scratch_ne (ofString "j") (Or.inr (Or.inl rfl))).2) hp.2.2.2.1
        · exact ptxPhase2D_scal_setVar_other s (.val (.word 0)) (ofString "j")
            ((ptxPhase2D_scratch_ne (ofString "j") (Or.inr (Or.inl rfl))).1) hp.2.2.2.2.1
      · exact ptxPhase2D_innerTail_hoare h
      · intro F r s locals hl hp hr
        exact ⟨ptxPhase2BX_with_locals s locals s.clock
            (fun n hn => hl n (ptxPhase2BXNames_sub_D2DecNames hn)) (hp hr).1,
          phase2_packed_nal_iteration_with_locals s locals s.clock (hp hr).2.1
            (fun n hn => hl n (nalNames_sub_D2DecNames hn)),
          phase2_accessCountReady_with_locals s locals s.clock
            (fun n hn => hl n (ptxPhase2DACRNames_sub_D2DecNames hn)) (hp hr).2.2.1,
          ptxPhase2D_fullR_with_locals s locals s.clock
            (fun n hn => hl n (ptxPhase2DDNames_sub_D2DecNames hn))
            (hl "al_keys" ptxPhase2DDecNames_al_keys) (hp hr).2.2.2.1,
          ptxPhase2D_scal_with_locals s locals s.clock
            (fun n hn => hl n (ptxPhase2DDNames_sub_D2DecNames hn)) (hp hr).2.2.2.2⟩
      · exact fun _ _ hr => by cases hr
    · intro F r s locals hl hp hr
      exact ⟨ptxPhase2BX_with_locals s locals s.clock
          (fun n hn => hl n (ptxPhase2BXNames_sub_D2DecNames hn)) (hp hr).1,
        phase2_packed_nal_iteration_with_locals s locals s.clock (hp hr).2.1
          (fun n hn => hl n (nalNames_sub_D2DecNames hn)),
        phase2_accessCountReady_with_locals s locals s.clock
          (fun n hn => hl n (ptxPhase2DACRNames_sub_D2DecNames hn)) (hp hr).2.2.1,
        ptxPhase2D_fullR_with_locals s locals s.clock
          (fun n hn => hl n (ptxPhase2DDNames_sub_D2DecNames hn))
          (hl "al_keys" ptxPhase2DDecNames_al_keys) (hp hr).2.2.2.1,
        ptxPhase2D_scal_with_locals s locals s.clock
          (fun n hn => hl n (ptxPhase2DDNames_sub_D2DecNames hn)) (hp hr).2.2.2.2⟩
    · exact fun _ _ hr => by cases hr
  · intro F r s locals hl hp hr
    exact ⟨ptxPhase2BX_with_locals s locals s.clock
        (fun n hn => hl n (ptxPhase2BXNames_sub_D2DecNames hn)) (hp hr).1,
      phase2_packed_nal_iteration_with_locals s locals s.clock (hp hr).2.1
        (fun n hn => hl n (nalNames_sub_D2DecNames hn)),
      phase2_accessCountReady_with_locals s locals s.clock
        (fun n hn => hl n (ptxPhase2DACRNames_sub_D2DecNames hn)) (hp hr).2.2.1,
      ptxPhase2D_fullR_with_locals s locals s.clock
        (fun n hn => hl n (ptxPhase2DDNames_sub_D2DecNames hn))
        (hl "al_keys" ptxPhase2DDecNames_al_keys) (hp hr).2.2.2.1,
      ptxPhase2D_scal_with_locals s locals s.clock
        (fun n hn => hl n (ptxPhase2DDNames_sub_D2DecNames hn)) (hp hr).2.2.2.2⟩
  · exact fun _ _ hr => by cases hr

/-! ### The outer packing loop -/

/-- The outer packing loop over `nal` retains every strengthened conjunct and
finishes with the cached count equal to the packed record count. -/
theorem ptxPhase2D_nalWhile_hoare {contents : Nat → BitVec 64} {E T A N : Nat}
    {body : ProgHOL 64}
    (hb : Hoare (fun s => ptxPhase2BX s ∧ PtxPackedNalIteration s ∧ PtxAccessCountReady s ∧
        ptxPhase2DFullR contents E T A N s ∧ ptxPhase2DScal s ∧
      locN s "i" < memW s (locN s "tx" + 216)) body
      (fun r s => r = none → ptxPhase2BX s ∧ PtxPackedNalIteration s ∧
        PtxAccessCountReady s ∧ ptxPhase2DFullR contents E T A N s ∧ ptxPhase2DScal s))
    (hnb : InitECandidate.Solver.GuestUniformClockBound.noTopBreak body = true)
    (hnc : InitECandidate.Solver.PanRunBounded.noTopContinue body = true) :
    Hoare (fun s => ptxPhase2BX s ∧ PtxPackedNalIteration s ∧ PtxAccessCountReady s ∧
        ptxPhase2DFullR contents E T A N s ∧ ptxPhase2DScal s)
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nal"))) body)
      (fun r s => r = none → ptxPhase2BX s ∧ PtxPackedNalIteration s ∧
        PtxAccessCountReady s ∧ ptxPhase2DFullR contents E T A N s ∧ ptxPhase2DScal s ∧
        locN s "k" = locN s "nkeys") := by
  let guard : ExpHOL 64 := .cmp .less (.var .local (ofString "i")) (.var .local (ofString "nal"))
  change Hoare (fun s => ptxPhase2BX s ∧ PtxPackedNalIteration s ∧ PtxAccessCountReady s ∧
      ptxPhase2DFullR contents E T A N s ∧ ptxPhase2DScal s) (.while guard body) _
  refine ⟨fun {F} s hc hp _ hr => ?_⟩
  generalize he : evaluateHOLFiniteState s (.while guard body) = out at hr ⊢
  obtain ⟨r, post⟩ := out
  dsimp only at hr
  subst r
  suffices ∀ (k : Nat) (st : PanSemStateFiniteExact 64 F), st.clock = k →
      st.code = originalRuntimeCode → ptxPhase2BX st ∧ PtxPackedNalIteration st ∧
        PtxAccessCountReady st ∧ ptxPhase2DFullR contents E T A N st ∧ ptxPhase2DScal st →
      evaluateHOLFiniteState st (.while guard body) = (none, post) →
      ptxPhase2BX post ∧ PtxPackedNalIteration post ∧ PtxAccessCountReady post ∧
        ptxPhase2DFullR contents E T A N post ∧ ptxPhase2DScal post ∧
        locN post "k" = locN post "nkeys" from
    this s.clock s rfl hc hp he
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro st hk hc hp he
    rw [evaluateHOLFiniteState_while_total] at he
    split at he
    · rename_i w hw
      have hguard := phase2_packed_outer_nal_guard st w hp.2.1.1 hp.2.1.2.1 hp.2.1.2.2
        (by simpa [evalAt, guard] using hw)
      split at he
      · rename_i hnz
        split at he
        · simp at he
        · dsimp only at he
          rw [fixClockHOLFinite_evaluateState] at he
          have hd := phase2_packed_nal_iteration_decClock st hp.2.1
          have hdACR := ptxPhase2D_acr_decClock hp.2.2.1
          have hdFullR := ptxPhase2D_fullR_decClock hp.2.2.2.1
          have hdScal := ptxPhase2D_scal_decClock hp.2.2.2.2
          have hm := (InitECandidate.Solver.PanRunBounded.evaluateHOLFiniteState_metadata
            (decClockHOLFinite st) body).1
          have hclk := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) body
          have hbr := InitECandidate.Solver.GuestUniformClockBound.evaluate_noTopBreak body hnb
            (decClockHOLFinite st)
          have hco := InitECandidate.Solver.PanRunBounded.evaluate_noTopContinue body hnc
            (decClockHOLFinite st)
          rcases hrun : evaluateHOLFiniteState (decClockHOLFinite st) body with ⟨r, mid⟩
          rw [hrun] at he hm hclk hbr hco
          cases r with
          | none =>
            have hmid := hb.run (decClockHOLFinite st) hc
              ⟨ptxPhase2BX_decClock st hp.1,
                ⟨hd, ⟨hdACR, ⟨hdFullR, ⟨hdScal, hguard.mp hnz⟩⟩⟩⟩⟩
              (by rw [hrun]; simp) (by rw [hrun])
            rw [hrun] at hmid
            apply ih mid.clock (by change mid.clock ≤ st.clock - 1 at hclk; omega)
              mid rfl (hm.trans hc) hmid he
          | some r => cases r <;> simp_all
      · rename_i hz
        simp at he
        obtain ⟨_, rfl⟩ := he
        exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2,
          (phase2_packed_outer_exit hp.2.1.1.2.1 (fun hlt => hz (hguard.mpr hlt))).2⟩
    · simp at he

/-- The concrete outer packing loop completes all records while retaining
every strengthened conjunct. -/
theorem ptxPhase2D_outerWhile_hoare (h : PtxCallees) {contents : Nat → BitVec 64} {E T A N : Nat} :
    Hoare (fun s => ptxPhase2BX s ∧ PtxPackedNalIteration s ∧ PtxAccessCountReady s ∧
        ptxPhase2DFullR contents E T A N s ∧ ptxPhase2DScal s)
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nal")))
        phase2_packed_source_outer_body)
      (fun r s => r = none → ptxPhase2BX s ∧ PtxPackedNalIteration s ∧
        PtxAccessCountReady s ∧ ptxPhase2DFullR contents E T A N s ∧ ptxPhase2DScal s ∧
        locN s "k" = locN s "nkeys") :=
  ptxPhase2D_nalWhile_hoare (ptxPhase2D_outerBody_hoare h) rfl rfl

/-- The source packing loop discharges into the packed-keys readiness with
the glue conjunct and the strengthened conjuncts, on both the enabled and
the disabled branch. -/
theorem ptxPhase2D_packedWhile_hoare (h : PtxCallees) {contents : Nat → BitVec 64} {E T A N : Nat} :
    Hoare (fun s => (ptxPhase2BX s ∧ PtxPackedNalIteration s ∧ PtxAccessCountReady s ∧
          ptxPhase2DFullR contents E T A N s ∧ ptxPhase2DScal s) ∨
        (ptxPhase2BX s ∧ PtxAccessCountReady s ∧ ptxPhase2DFullR contents E T A N s ∧
          ptxPhase2DScal s ∧ PtxPackedKeysReady s ∧
          s.locals.lookup (ofString "i") = some (.val (.word 0)) ∧
          s.locals.lookup (ofString "nal") = some (.val (.word 0))))
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nal")))
        phase2_packed_source_outer_body)
      (fun r s => r = none → ptxPhase2BX s ∧ PtxPackedKeysReady s ∧ PtxAccessCountReady s ∧
        ptxPhase2DFullR contents E T A N s ∧ ptxPhase2DScal s) := by
  refine ⟨fun {F} s hc hp hnt hr => ?_⟩
  rcases hp with hp | hp
  · have hout := (ptxPhase2D_outerWhile_hoare h).run s hc hp hnt hr
    exact ⟨hout.1, hout.2.1.1.2.1.1, hout.2.2.1, hout.2.2.2.1, hout.2.2.2.2.1⟩
  · rw [phase2_zero_nal_loop s phase2_packed_source_outer_body hp.2.2.2.2.2.1 hp.2.2.2.2.2.2]
    exact ⟨hp.1, hp.2.2.2.2.1, hp.2.1, hp.2.2.1, hp.2.2.2.1⟩

/-! ## The region-D exit -/

/-- The packed-keys readiness together with the strengthened conjuncts
implies the region-D exit invariant. -/
theorem ptxPhase2D_crExit {contents : Nat → BitVec 64} {E T A N : Nat}
    {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : ptxPhase2BX s ∧ PtxPackedKeysReady s ∧ PtxAccessCountReady s ∧
      ptxPhase2DFullR contents E T A N s ∧ ptxPhase2DScal s) :
    ptxPhase2CRInv s ∧ PtxPhase2X s := by
  obtain ⟨hbx, hkeys, hacr, hfull, hscal⟩ := hp
  obtain ⟨he, hx, ha, hn, S, Nd, hW, hT, hlb1, hlb2, hlb3, hdTE, hrd⟩ := hfull.1
  refine ⟨⟨hacr, hscal.2.2.1, hkeys.1, hscal.2.2.2.1, ?_, ?_⟩, hbx.1⟩
  · refine ⟨S, Nd, hW, ?_, ?_, ?_⟩
    · rw [hx]; exact hT
    · rw [ha, hn]; exact hlb2.2.1
    · rw [he]; exact hlb1.2.1
  · rw [ha, hn]; exact hlb2.1

/-! ## The region-D loop bounds -/

/-- Two copies and the two clock-neutral counter assignments give the exact
active inner-body budget used by the source Phase 2 cost, under the
strengthened conjuncts. -/
theorem ptxPhase2D_body_bound (h : PtxCallees) (addressSrc keySrc : ExpHOL 64)
    {contents : Nat → BitVec 64} {E T A N : Nat} :
    TerminatingProgBoundedOn (fun s => ptxPhase2BX s ∧ PtxPackedNsNalCopy s ∧
        PtxAccessCountReady s ∧ ptxPhase2DFullR contents E T A N s ∧ ptxPhase2DScal s)
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
  have hc : TerminatingProgBoundedOn (fun s => ptxPhase2BX s ∧ PtxPackedNsNalCopy s ∧
        PtxAccessCountReady s ∧ ptxPhase2DFullR contents E T A N s ∧ ptxPhase2DScal s)
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
    (fun t hct hpt => phase2_packed_ns_nal_memcpy_bound h _ t hct hpt.2.1)
    (ptxPhase2D_address_copy_hoare h addressSrc)
    (fun t ht hpt => seq_bound_trans
      (fun t' hct' hpt' => phase2_packed_ns_nal_memcpy_bound h _ t' hct' hpt'.2.1)
      (ptxPhase2D_storage_copy_hoare h keySrc) hc t ht hpt) s hcode hp

/-- The cached-count inner loop has a uniform rank bound once its active body
bound is supplied, under the strengthened conjuncts. -/
theorem ptxPhase2D_innerWhile_bound {contents : Nat → BitVec 64} {E T A N : Nat}
    {body : ProgHOL 64} {B : Nat}
    (hb : Hoare (fun s => ptxPhase2BX s ∧ PtxPackedNsNalCopy s ∧ PtxAccessCountReady s ∧
        ptxPhase2DFullR contents E T A N s ∧ ptxPhase2DScal s) body
      (fun r s => r = none → ptxPhase2BX s ∧ PtxPackedNsNalIteration s ∧
        PtxAccessCountReady s ∧ ptxPhase2DFullR contents E T A N s ∧ ptxPhase2DScal s))
    (hbody : TerminatingProgBoundedOn (fun s => ptxPhase2BX s ∧ PtxPackedNsNalCopy s ∧
        PtxAccessCountReady s ∧ ptxPhase2DFullR contents E T A N s ∧ ptxPhase2DScal s) body B)
    (hinc : IncrBody (ofString "j") body) :
    TerminatingProgBoundedOn (fun s => ptxPhase2BX s ∧ PtxPackedNsNalIteration s ∧
        PtxAccessCountReady s ∧ ptxPhase2DFullR contents E T A N s ∧ ptxPhase2DScal s)
      (.while (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "ns"))) body)
      ((2 ^ 63 + 1) * (B + 1)) := by
  apply TerminatingProgBoundedOn.while_rank_active (fun s => 2 ^ 63 - locN s "j")
  · intro F s hp
    exact ⟨ptxPhase2BX_decClock s hp.1,
      ⟨phase2_packed_ns_iteration_decClock s hp.2.1.1, hp.2.1.2⟩,
      ptxPhase2D_acr_decClock hp.2.2.1, ptxPhase2D_fullR_decClock hp.2.2.2.1,
      ptxPhase2D_scal_decClock hp.2.2.2.2⟩
  · intro F s hc hp
    obtain ⟨w, hw, hnz⟩ := hp.2
    have hg := (phase2_packed_ns_guard_eval s w hp.1.2.1.1 hw).mp hnz
    exact hbody s hc ⟨hp.1.1,
      ⟨⟨phase2_packed_iteration_guard_pre s hp.1.2.1.1.1 hg, hp.1.2.1.1.2⟩, hp.1.2.1.2⟩,
      hp.1.2.2.1, hp.1.2.2.2.1, hp.1.2.2.2.2⟩
  · intro F s hc hp ha
    omega
  · intro F s hc hp ha hf
    obtain ⟨w, hw, hnz⟩ := ha
    have hg := (phase2_packed_ns_guard_eval s w hp.2.1.1 hw).mp hnz
    have hd : ptxPhase2BX (decClockHOLFinite s) ∧ PtxPackedNsNalIteration
        (decClockHOLFinite s) ∧ PtxAccessCountReady (decClockHOLFinite s) ∧
        ptxPhase2DFullR contents E T A N (decClockHOLFinite s) ∧
        ptxPhase2DScal (decClockHOLFinite s) :=
      ⟨ptxPhase2BX_decClock s hp.1,
        ⟨phase2_packed_ns_iteration_decClock s hp.2.1.1, hp.2.1.2⟩,
        ptxPhase2D_acr_decClock hp.2.2.1, ptxPhase2D_fullR_decClock hp.2.2.2.1,
        ptxPhase2D_scal_decClock hp.2.2.2.2⟩
    obtain ⟨j, hj⟩ := hp.2.1.1.1.2.2.2.1
    obtain ⟨hnc, hnext⟩ := hinc.run (decClockHOLFinite s) j hj
    have hnone := hf.resolve_right hnc
    have hpost := hb.run (decClockHOLFinite s) hc
      ⟨ptxPhase2BX_decClock s hp.1,
        ⟨⟨phase2_packed_iteration_guard_pre _ hd.2.1.1.1 hg, hd.2.1.1.2⟩, hd.2.1.2⟩,
        hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2⟩
      (by rw [hnone]; simp) hnone
    refine ⟨hpost, ?_⟩
    have hjn : locN s "j" = j.toNat := by simp [locN, hj]
    have hlt := (phase2_packed_inner_signed_bounds hp.2.1.1.1.2.1.1).1
    have hpl := (phase2_packed_inner_signed_bounds hpost.2.1.1.1.2.1.1).1
    have hpn : locN (evaluateHOLFiniteState (decClockHOLFinite s) body).2 "j" =
        (j.toNat + 1) % 2 ^ 64 := by
      simp [locN, hnext hnone, BitVec.toNat_add]
    rw [hjn] at hlt ⊢
    rw [hpn]
    have hmod : (j.toNat + 1) % 2 ^ 64 = j.toNat + 1 := Nat.mod_eq_of_lt (by omega)
    rw [hmod] at *
    omega

/-- The actual source inner loop and following record increment have the
advertised nested-loop clock budget, under the strengthened conjuncts. -/
theorem ptxPhase2D_innerTail_bound (h : PtxCallees) {contents : Nat → BitVec 64} {E T A N : Nat} :
    TerminatingProgBoundedOn (fun s => ptxPhase2BX s ∧ PtxPackedNsNalIteration s ∧
        PtxAccessCountReady s ∧ ptxPhase2DFullR contents E T A N s ∧ ptxPhase2DScal s)
      phase2_packed_source_inner_tail
      ((2 ^ 63 + 1) * ((K.memcpy + 1) + (K.memcpy + 1) + 1)) := by
  unfold phase2_packed_source_inner_tail
  have hb : TerminatingProgBoundedOn (fun s => ptxPhase2BX s ∧ PtxPackedNsNalIteration s ∧
      PtxAccessCountReady s ∧ ptxPhase2DFullR contents E T A N s ∧ ptxPhase2DScal s) _
      ((2 ^ 63 + 1) * ((K.memcpy + 1) + (K.memcpy + 1) + 1)) :=
    ptxPhase2D_innerWhile_bound
      (ptxPhase2D_body_hoare h
        (.load .one (.op .add [.var .local (ofString "acc2"), .const 0]))
        (.op .add [.load .one (.op .add [.var .local (ofString "acc2"), .const 8]),
          .panop .mul [.var .local (ofString "j"), .const 32]]))
      (ptxPhase2D_body_bound h
        (.load .one (.op .add [.var .local (ofString "acc2"), .const 0]))
        (.op .add [.load .one (.op .add [.var .local (ofString "acc2"), .const 8]),
          .panop .mul [.var .local (ofString "j"), .const 32]]))
      (by ptx_incr)
  have ht : TerminatingProgBoundedOn
      (fun s => ptxPhase2BX s ∧ PtxPackedNsNalIteration s ∧ PtxAccessCountReady s ∧
        ptxPhase2DFullR contents E T A N s ∧ ptxPhase2DScal s ∧
        locN s "k" = phase2_key_prefix s (locN s "i" + 1))
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])) 0 := by
    intro F s hc hp hn
    rw [clock_assign]
    exact ⟨by omega, le_rfl⟩
  intro F s hc hp
  simpa only [Nat.add_zero] using seq_bound_trans hb
    (ptxPhase2D_innerWhile_hoare
      (ptxPhase2D_body_hoare h
        (.load .one (.op .add [.var .local (ofString "acc2"), .const 0]))
        (.op .add [.load .one (.op .add [.var .local (ofString "acc2"), .const 8]),
          .panop .mul [.var .local (ofString "j"), .const 32]]))
      (by decide) (by decide)) ht s hc hp

/-- The record-local declarations preserve the inner-loop clock budget,
under the strengthened conjuncts. -/
theorem ptxPhase2D_outerBody_bound (h : PtxCallees) {contents : Nat → BitVec 64} {E T A N : Nat} :
    TerminatingProgBoundedOn (fun s => ptxPhase2BX s ∧ PtxPackedNalIteration s ∧
        PtxAccessCountReady s ∧ ptxPhase2DFullR contents E T A N s ∧ ptxPhase2DScal s ∧
      locN s "i" < memW s (locN s "tx" + 216)) phase2_packed_source_outer_body
      ((2 ^ 63 + 1) * ((K.memcpy + 1) + (K.memcpy + 1) + 1)) := by
  unfold phase2_packed_source_outer_body
  apply dec_bound_trans (Q := fun s => ptxPhase2BX s ∧ PtxPackedNalIteration s ∧
    PtxAccessCountReady s ∧ ptxPhase2DFullR contents E T A N s ∧ ptxPhase2DScal s ∧
    locN s "i" < memW s (locN s "tx" + 216) ∧
    locN s "acc2" = memW s (locN s "tx" + 208) + 24 * locN s "i")
  · intro F s v hp he
    have hd := phase2_packed_outer_declare_acc2 s hp.2.1.1 hp.2.2.2.2.2 v he
    exact ⟨ptxPhase2BX_setVar_scratch s v (ofString "acc2") hp.1
        (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
      phase2_packed_nal_set_other s hp.2.1 _ _ (by decide),
      ptxPhase2D_acr_setVar_scratch s v (ofString "acc2")
        (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hp.2.2.1,
      ptxPhase2D_fullR_setVar_other s v (ofString "acc2")
        ((ptxPhase2D_scratch_ne (ofString "acc2") (Or.inr (Or.inr (Or.inr (Or.inl rfl))))).1)
        ((ptxPhase2D_scratch_ne (ofString "acc2") (Or.inr (Or.inr (Or.inr (Or.inl rfl))))).2)
        hp.2.2.2.1,
      ptxPhase2D_scal_setVar_other s v (ofString "acc2")
        ((ptxPhase2D_scratch_ne (ofString "acc2") (Or.inr (Or.inr (Or.inr (Or.inl rfl))))).1)
        hp.2.2.2.2.1, hd.2⟩
  · apply dec_bound_trans (Q := fun s => ptxPhase2BX s ∧ PtxPackedNalIteration s ∧
      PtxAccessCountReady s ∧ ptxPhase2DFullR contents E T A N s ∧ ptxPhase2DScal s ∧
      locN s "i" < memW s (locN s "tx" + 216) ∧
      (∃ n : BitVec 64, s.locals.lookup (ofString "ns") = some (.val (.word n))) ∧
      locN s "ns" = memW s (memW s (locN s "tx" + 208) + 24 * locN s "i" + 16))
    · intro F s v hp he
      have hd := phase2_packed_outer_declare_ns s hp.2.1.1 hp.2.2.2.2.2.1 hp.2.2.2.2.2.2 v he
      exact ⟨ptxPhase2BX_setVar_scratch s v (ofString "ns") hp.1
          (Or.inr (Or.inr (Or.inr (Or.inr rfl)))),
        phase2_packed_nal_set_other s hp.2.1 _ _ (by decide),
        ptxPhase2D_acr_setVar_scratch s v (ofString "ns")
          (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hp.2.2.1,
        ptxPhase2D_fullR_setVar_other s v (ofString "ns")
          ((ptxPhase2D_scratch_ne (ofString "ns") (Or.inr (Or.inr (Or.inr (Or.inr rfl))))).1)
          ((ptxPhase2D_scratch_ne (ofString "ns") (Or.inr (Or.inr (Or.inr (Or.inr rfl))))).2)
          hp.2.2.2.1,
        ptxPhase2D_scal_setVar_other s v (ofString "ns")
          ((ptxPhase2D_scratch_ne (ofString "ns") (Or.inr (Or.inr (Or.inr (Or.inr rfl))))).1)
          hp.2.2.2.2.1, hd.2⟩
    · apply dec_bound_trans (Q := fun s => ptxPhase2BX s ∧ PtxPackedNsNalIteration s ∧
        PtxAccessCountReady s ∧ ptxPhase2DFullR contents E T A N s ∧ ptxPhase2DScal s)
      · intro F s v hp he
        have hv : v = .val (.word 0) := by simpa [evalAt, evalHOLExact] using he.symm
        subst v
        exact ⟨ptxPhase2BX_setVar_scratch s (.val (.word 0)) (ofString "j") hp.1
            (Or.inr (Or.inl rfl)),
          ⟨phase2_packed_ns_reset s hp.2.1.1 hp.2.2.2.2.2.1 hp.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2,
            (phase2_packed_nal_set_other s hp.2.1 (ofString "j") (.val (.word 0))
              (by decide)).2⟩,
          ptxPhase2D_acr_setVar_scratch s (.val (.word 0)) (ofString "j")
            (Or.inr (Or.inl rfl)) hp.2.2.1,
          ptxPhase2D_fullR_setVar_other s (.val (.word 0)) (ofString "j")
            ((ptxPhase2D_scratch_ne (ofString "j") (Or.inr (Or.inl rfl))).1)
            ((ptxPhase2D_scratch_ne (ofString "j") (Or.inr (Or.inl rfl))).2) hp.2.2.2.1,
          ptxPhase2D_scal_setVar_other s (.val (.word 0)) (ofString "j")
            ((ptxPhase2D_scratch_ne (ofString "j") (Or.inr (Or.inl rfl))).1) hp.2.2.2.2.1⟩
      · exact ptxPhase2D_innerTail_bound h

/-- A decreasing record counter bounds the concrete outer packing loop,
under the strengthened conjuncts. -/
theorem ptxPhase2D_outerWhile_bound (h : PtxCallees) {contents : Nat → BitVec 64} {E T A N : Nat} :
    TerminatingProgBoundedOn (fun s => ptxPhase2BX s ∧ PtxPackedNalIteration s ∧
        PtxAccessCountReady s ∧ ptxPhase2DFullR contents E T A N s ∧ ptxPhase2DScal s)
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nal")))
        phase2_packed_source_outer_body)
      ((2 ^ 63 + 1) * ((2 ^ 63 + 1) * ((K.memcpy + 1) + (K.memcpy + 1) + 1) + 1)) := by
  apply TerminatingProgBoundedOn.while_rank_active (fun s => 2 ^ 63 - locN s "i")
  · intro F s hp
    exact ⟨ptxPhase2BX_decClock s hp.1, phase2_packed_nal_iteration_decClock s hp.2.1,
      ptxPhase2D_acr_decClock hp.2.2.1, ptxPhase2D_fullR_decClock hp.2.2.2.1,
      ptxPhase2D_scal_decClock hp.2.2.2.2⟩
  · intro F s hc hp
    obtain ⟨w, hw, hnz⟩ := hp.2
    have hg := (phase2_packed_outer_nal_guard s w hp.1.2.1.1 hp.1.2.1.2.1 hp.1.2.1.2.2 hw).mp hnz
    exact ptxPhase2D_outerBody_bound h s hc
      ⟨hp.1.1, hp.1.2.1, hp.1.2.2.1, hp.1.2.2.2.1, hp.1.2.2.2.2, hg⟩
  · intro F s hc hp ha
    omega
  · intro F s hc hp ha hf
    obtain ⟨w, hw, hnz⟩ := ha
    have hg := (phase2_packed_outer_nal_guard s w hp.2.1.1 hp.2.1.2.1 hp.2.1.2.2 hw).mp hnz
    have hd := phase2_packed_nal_iteration_decClock s hp.2.1
    have hdACR := ptxPhase2D_acr_decClock hp.2.2.1
    have hdFullR := ptxPhase2D_fullR_decClock hp.2.2.2.1
    have hdScal := ptxPhase2D_scal_decClock hp.2.2.2.2
    have hinc : IncrBody (ofString "i") phase2_packed_source_outer_body := by
      unfold phase2_packed_source_outer_body phase2_packed_source_inner_tail
      ptx_incr
    obtain ⟨i, hi⟩ := hp.2.1.1.2.2.2.2.2.1
    obtain ⟨hnc, hnext⟩ := hinc.run (decClockHOLFinite s) i hi
    have hnone := hf.resolve_right hnc
    have hpost := (ptxPhase2D_outerBody_hoare h).run
      (decClockHOLFinite s) hc ⟨ptxPhase2BX_decClock s hp.1, hd, hdACR, hdFullR, hdScal, hg⟩
      (by rw [hnone]; simp) hnone
    refine ⟨hpost, ?_⟩
    have hin : locN s "i" = i.toNat := by simp [locN, hi]
    have hlt := (phase2_packed_outer_signed_bounds hp.2.1.1).1
    have hpn : locN (evaluateHOLFiniteState (decClockHOLFinite s)
        phase2_packed_source_outer_body).2 "i" = (i.toNat + 1) % 2 ^ 64 := by
      simp [locN, hnext hnone, BitVec.toNat_add]
    rw [hin] at hlt ⊢
    rw [hpn, Nat.mod_eq_of_lt (by omega : i.toNat + 1 < 2 ^ 64)]
    omega

/-! ## The region-D segment bound -/

/-- Counter initialization, either packing branch, and the trailing statements
inside the declaration share the concrete packing-loop budget, under the
strengthened conjuncts. -/
theorem ptxPhase2D_packedInitTail_bound (h : PtxCallees) {contents : Nat → BitVec 64}
    {E T A N : Nat} {tail : ProgHOL 64} {b : Nat}
    (ht : TerminatingProgBoundedOn (fun s => ptxPhase2BX s ∧ PtxPackedKeysReady s ∧
        PtxAccessCountReady s ∧ ptxPhase2DFullR contents E T A N s ∧ ptxPhase2DScal s) tail b) :
    TerminatingProgBoundedOn (fun s => ptxPhase2BX s ∧ PtxPackedInitCases s ∧
        ptxPhase2DFullR contents E T A N s ∧ ptxPhase2DScal s ∧ PtxAccessCountReady s)
      (.dec (ofString "k") .one (.const 0)
        (.seq (.assign .local (ofString "i") (.const 0))
          (.seq (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nal")))
            phase2_packed_source_outer_body) tail)))
      ((2 ^ 63 + 1) * ((2 ^ 63 + 1) * ((K.memcpy + 1) + (K.memcpy + 1) + 1) + 1) + b) := by
  apply dec_bound_trans (Q := fun s =>
    ∃ before, (ptxPhase2BX before ∧ PtxPackedInitCases before ∧
      ptxPhase2DFullR contents E T A N before ∧ ptxPhase2DScal before ∧
      PtxAccessCountReady before) ∧
      s = setVarHOLFinite (ofString "k") (.val (.word 0)) before)
  · intro F s v hp he
    have hv : v = .val (.word 0) := by simpa [evalAt, evalHOLExact] using he.symm
    subst v
    exact ⟨s, hp, rfl⟩
  · have ha : Hoare (fun s => ∃ before, (ptxPhase2BX before ∧ PtxPackedInitCases before ∧
        ptxPhase2DFullR contents E T A N before ∧ ptxPhase2DScal before ∧
        PtxAccessCountReady before) ∧
        s = setVarHOLFinite (ofString "k") (.val (.word 0)) before)
      (.assign .local (ofString "i") (.const 0))
      (fun r s => r = none → (ptxPhase2BX s ∧ PtxPackedNalIteration s ∧
          PtxAccessCountReady s ∧ ptxPhase2DFullR contents E T A N s ∧ ptxPhase2DScal s) ∨
        (ptxPhase2BX s ∧ PtxAccessCountReady s ∧ ptxPhase2DFullR contents E T A N s ∧
          ptxPhase2DScal s ∧ PtxPackedKeysReady s ∧
          s.locals.lookup (ofString "i") = some (.val (.word 0)) ∧
          s.locals.lookup (ofString "nal") = some (.val (.word 0)))) := by
      apply Hoare.assign
      · intro F s v hp he
        obtain ⟨before, hp, rfl⟩ := hp
        have hv : v = .val (.word 0) := by simpa [evalAt, evalHOLExact] using he.symm
        subst v
        intro _
        have hbx : ptxPhase2BX (setVarHOLFinite (ofString "k") (.val (.word 0)) before) :=
          ptxPhase2BX_setVar_scratch before (.val (.word 0)) (ofString "k") hp.1
            (Or.inl rfl)
        have hacr : PtxAccessCountReady (setVarHOLFinite (ofString "k") (.val (.word 0)) before) :=
          ptxPhase2D_acr_setVar_scratch before _ (ofString "k") (Or.inl rfl) hp.2.2.2.2
        have hfull : ptxPhase2DFullR contents E T A N
            (setVarHOLFinite (ofString "k") (.val (.word 0)) before) :=
          ptxPhase2D_fullR_setVar_other before _ (ofString "k")
            ((ptxPhase2D_scratch_ne (ofString "k") (Or.inl rfl)).1)
            ((ptxPhase2D_scratch_ne (ofString "k") (Or.inl rfl)).2) hp.2.2.1
        have hscal : ptxPhase2DScal (setVarHOLFinite (ofString "k") (.val (.word 0)) before) :=
          ptxPhase2D_scal_setVar_other before _ (ofString "k")
            ((ptxPhase2D_scratch_ne (ofString "k") (Or.inl rfl)).1) hp.2.2.2.1
        rcases hp.2.1 with hcases | hcases
        · exact Or.inl ⟨ptxPhase2BX_setVar_scratch _ (.val (.word 0)) (ofString "i") hbx
            (Or.inr (Or.inr (Or.inl rfl))),
            phase2_packed_init_state before hcases,
            ptxPhase2D_acr_setVar_scratch _ _ (ofString "i")
              (Or.inr (Or.inr (Or.inl rfl))) hacr,
            ptxPhase2D_fullR_setVar_other _ _ (ofString "i")
              ((ptxPhase2D_scratch_ne (ofString "i") (Or.inr (Or.inr (Or.inl rfl)))).1)
              ((ptxPhase2D_scratch_ne (ofString "i") (Or.inr (Or.inr (Or.inl rfl)))).2) hfull,
            ptxPhase2D_scal_setVar_other _ _ (ofString "i")
              ((ptxPhase2D_scratch_ne (ofString "i") (Or.inr (Or.inr (Or.inl rfl)))).1) hscal⟩
        · exact Or.inr ⟨ptxPhase2BX_setVar_scratch _ (.val (.word 0)) (ofString "i") hbx
            (Or.inr (Or.inr (Or.inl rfl))),
            ptxPhase2D_acr_setVar_scratch _ _ (ofString "i")
              (Or.inr (Or.inr (Or.inl rfl))) hacr,
            ptxPhase2D_fullR_setVar_other _ _ (ofString "i")
              ((ptxPhase2D_scratch_ne (ofString "i") (Or.inr (Or.inr (Or.inl rfl)))).1)
              ((ptxPhase2D_scratch_ne (ofString "i") (Or.inr (Or.inr (Or.inl rfl)))).2) hfull,
            ptxPhase2D_scal_setVar_other _ _ (ofString "i")
              ((ptxPhase2D_scratch_ne (ofString "i") (Or.inr (Or.inr (Or.inl rfl)))).1) hscal,
            phase2_packed_zero_init before hcases.1 hcases.2⟩
      · exact fun _ _ hr => by cases hr
    have hb : TerminatingProgBoundedOn
        (fun s => ∃ before, (ptxPhase2BX before ∧ PtxPackedInitCases before ∧
          ptxPhase2DFullR contents E T A N before ∧ ptxPhase2DScal before ∧
          PtxAccessCountReady before) ∧
          s = setVarHOLFinite (ofString "k") (.val (.word 0)) before)
        (.assign .local (ofString "i") (.const 0)) 0 := by
      intro F s hc hp hn
      rw [clock_assign]
      exact ⟨by omega, le_rfl⟩
    have hl : TerminatingProgBoundedOn
        (fun s => (ptxPhase2BX s ∧ PtxPackedNalIteration s ∧ PtxAccessCountReady s ∧
            ptxPhase2DFullR contents E T A N s ∧ ptxPhase2DScal s) ∨
          (ptxPhase2BX s ∧ PtxAccessCountReady s ∧ ptxPhase2DFullR contents E T A N s ∧
            ptxPhase2DScal s ∧ PtxPackedKeysReady s ∧
            s.locals.lookup (ofString "i") = some (.val (.word 0)) ∧
            s.locals.lookup (ofString "nal") = some (.val (.word 0))))
        (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nal")))
          phase2_packed_source_outer_body)
        ((2 ^ 63 + 1) * ((2 ^ 63 + 1) * ((K.memcpy + 1) + (K.memcpy + 1) + 1) + 1)) := by
      intro F s hc hp hn
      rcases hp with hp | hp
      · exact ptxPhase2D_outerWhile_bound h s hc hp hn
      · rw [phase2_zero_nal_loop s phase2_packed_source_outer_body hp.2.2.2.2.2.1 hp.2.2.2.2.2.2]
        exact ⟨by dsimp; omega, le_rfl⟩
    have hinner : TerminatingProgBoundedOn
        (fun s => (ptxPhase2BX s ∧ PtxPackedNalIteration s ∧ PtxAccessCountReady s ∧
            ptxPhase2DFullR contents E T A N s ∧ ptxPhase2DScal s) ∨
          (ptxPhase2BX s ∧ PtxAccessCountReady s ∧ ptxPhase2DFullR contents E T A N s ∧
            ptxPhase2DScal s ∧ PtxPackedKeysReady s ∧
            s.locals.lookup (ofString "i") = some (.val (.word 0)) ∧
            s.locals.lookup (ofString "nal") = some (.val (.word 0))))
        (.seq (.while (.cmp .less (.var .local (ofString "i"))
            (.var .local (ofString "nal"))) phase2_packed_source_outer_body) tail)
        ((2 ^ 63 + 1) * ((2 ^ 63 + 1) * ((K.memcpy + 1) + (K.memcpy + 1) + 1) + 1) + b) := by
      intro F s hc hp hn
      exact seq_bound_trans hl (ptxPhase2D_packedWhile_hoare h) ht s hc hp hn
    intro F s hc hp
    simpa only [Nat.zero_add] using seq_bound_trans hb ha hinner s hc hp

/-! ## Region D segment bound (guest spine 49..52) -/

/-- The packed-key allocation and packing loop compose with the tail into the
region-D exit invariant. -/
theorem ptxPhase2D_packedCR_bound (h : PtxCallees) {contents : Nat → BitVec 64}
    {E T A N : Nat} {tail : ProgHOL 64} {b : Nat}
    (ht : TerminatingProgBoundedOn (fun s => ptxPhase2CRInv s ∧ PtxPhase2X s) tail b) :
    TerminatingProgBoundedOn (fun s => PtxAddressCountExit s ∧ PtxPhase2X s ∧
        ptxPhase2DFam contents E T A N s ∧ ptxPhase2DScal s)
      (spinePlug 4 (spineAt 49 ptxCode) tail)
      (K.alloc + ((2 ^ 63 + 1) * ((2 ^ 63 + 1) *
        ((K.memcpy + 1) + (K.memcpy + 1) + 1) + 1) + b) + 1) := by
  have he : spinePlug 4 (spineAt 49 ptxCode) tail =
      .decCall (ofString "al_keys") .one (ofString "alloc")
        [.op .add [.panop .mul [.var .local (ofString "nkeys"), .const 52], .const 8]]
        (.dec (ofString "k") .one (.const 0)
          (.seq (.assign .local (ofString "i") (.const 0))
            (.seq (.while (.cmp .less (.var .local (ofString "i"))
              (.var .local (ofString "nal"))) phase2_packed_source_outer_body) tail))) := by
    simp only [ptxCode, sourceFunctionEntry, Guest.Software.guestFn_process_transaction,
      spineAt, spinePlug]
    rfl
  rw [he]
  apply TerminatingProgBoundedOn.decCall_on
    (Q := fun s => ptxPhase2BX s ∧ PtxPackedInitCases s ∧
      ptxPhase2DFullR contents E T A N s ∧ ptxPhase2DScal s ∧ PtxAccessCountReady s) h.fb_alloc
  · intro F s vs body callee ret hc hp ha hl
    have hr := phase2_count_exit_access_ready hp.1
    exact guestInv_callEntry s callee hr.1.1.1.1.1.1.1.1.1
  · exact ptxPhase2D_alKeys_resume h contents E T A N
  · exact ptxPhase2D_packedInitTail_bound h
      (R16Shards.PtxP1.bound_mono ht (fun _ hs => ptxPhase2D_crExit hs))

end InitECandidate.Solver.Wave8GuestInv.R13Shards
