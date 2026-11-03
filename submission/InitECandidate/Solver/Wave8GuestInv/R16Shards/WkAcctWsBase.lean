import InitECandidate.Solver.Wave8GuestInv.R10Shards.EvmFrameSpecs
import InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28_Inits

/-! Compositional `WorldStepSc` / `ProgWStep` framework and non-value table `HtabExit`
world-step lifting for C08 Account & WorldState `wk_*` contracts (`R16e-WkAcctWs`). -/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28

/-! ## 1. Untyped Global Buffer Lists & `WorldStepSc` -/

abbrev BufList := List (String × Nat)

def ValidBufList (B : BufList) : Prop :=
  ∀ p ∈ B, ∃ sz, (p.1, sz) ∈ globalBuffers ∧ p.1 ∉ ["ws", "bs", "ts", "bo"] ∧ p.2 ≤ sz

def bufRegions (B : BufList) {F : Type} (s : PanSemStateFiniteExact 64 F) : List Ivl :=
  B.map (bufferRegion s)

theorem validBufList_disj {F : Type} {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    {B : BufList} (hB : ValidBufList B) (hWT : WorldTypedWith s S Nd) :
    IvlsDisj (bufRegions B s) (worldTypedIvls s S Nd) := by
  intro i hi j hj
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hi
  obtain ⟨sz, hgb, hun, hle⟩ := hB p hp
  have hun' : (p.1, sz).1 ∉ typedRecords.map Prod.fst := by
    dsimp only
    simpa [typedRecords] using hun
  exact bufferRegion_disj_le hWT (p.1, sz) hgb hun' p.2 hle j hj

def SafeStepGlobals (gw : List String) : Prop :=
  ∀ g ∈ gw, g ∈ ["heap_ptr", "scratch_ptr", "journal_n"]

theorem SafeStepGlobals.not_mem_map {gw : List String} (h : SafeStepGlobals gw) {k : MlS}
    (hk : k ∉ (["heap_ptr", "scratch_ptr", "journal_n"] : List String).map ofString) :
    k ∉ gw.map ofString := by
  intro hm
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hm
  exact hk (List.mem_map.2 ⟨g, h g hg, rfl⟩)

theorem globalBuffers_not_stepGlobal {gp : String × Nat} (hgp : gp ∈ globalBuffers) :
    ofString gp.1 ∉ (["heap_ptr", "scratch_ptr", "journal_n"] : List String).map ofString := by
  revert gp hgp
  decide

theorem bufRegions_eq_of_safeGlobals {F : Type} {s1 s2 : PanSemStateFiniteExact 64 F}
    {B : BufList} {gw : List String} (hB : ValidBufList B) (hgw : SafeStepGlobals gw)
    (hG : GlobalsKept gw s1 s2) :
    bufRegions B s2 = bufRegions B s1 := by
  unfold bufRegions
  apply List.map_congr_left
  intro p hp
  obtain ⟨sz, hgb, _⟩ := hB p hp
  have hk := hgw.not_mem_map (globalBuffers_not_stepGlobal hgb)
  have hg_eq : globN s2 p.1 = globN s1 p.1 := globN_eq_of_lookup (hG (ofString p.1) hk)
  simp [bufferRegion, hg_eq]

/-- `WorldStep` strengthened with monotonic scratch pointer (`scratch_ptr` only shrinks or stays). -/
def WorldStepSc (R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl) (gw : List String)
    (keep : List (String × List Nat))
    (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop :=
  fun s r post => WorldStep R gw keep Q s r post ∧ globN post "scratch_ptr" ≤ globN s "scratch_ptr"

def WorldKeepsSc (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl) (gw : List String)
    (keep : List (String × List Nat))
    (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop) (fname : MlS) : Prop :=
  FunSpec P (fun s r post => Resumes r → WorldStepSc R gw keep Q s r post) fname

theorem WorldKeepsSc.to_worldKeeps {P R gw keep Q fname}
    (h : WorldKeepsSc P R gw keep Q fname) : WorldKeeps P R gw keep Q fname := by
  obtain ⟨ps, body, ret, hl, hb⟩ := h
  exact ⟨ps, body, ret, hl, fun s hc hP hex hnt hr => (hb s hc hP hex hnt hr).1⟩

theorem WorldStepSc.refl {F : Type}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    (s : PanSemStateFiniteExact 64 F) (r : Option (PanSemResultExact 64))
    (hA : ArenaReady s) :
    WorldStepSc R gw keep NoExtra s r s := by
  refine ⟨⟨hA, le_rfl, fun _ _ => rfl, fun _ _ _ _ _ _ => rfl, fun S Nd hWT _ => ?_⟩, le_rfl⟩
  exact ⟨S, Nd, fun _ h => h, hWT,
    fun o ho => Or.inr (Or.inl ⟨o, ho, le_rfl, le_rfl⟩),
    fun _ _ _ => rfl, trivial⟩

theorem WorldStepSc.with_locals_clock {F : Type}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    {s post : PanSemStateFiniteExact 64 F} {r r' : Option (PanSemResultExact 64)}
    (h : WorldStepSc R gw keep NoExtra s r post)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    WorldStepSc R gw keep NoExtra s r' { post with locals := L, clock := k } := by
  obtain ⟨⟨hAp, hhp, hG, hK, hW⟩, hsc⟩ := h
  refine ⟨⟨localsFree_arenaReady post L k hAp, hhp, hG, hK, fun S Nd hWT hD => ?_⟩, hsc⟩
  obtain ⟨S', Nd', hsub, hWT', hOG, hFO, _⟩ := hW S Nd hWT hD
  obtain ⟨hT', hJ', hF', hNH', hndisj', hws'⟩ := hWT'
  have hWT'' : WorldTypedWith { post with locals := L, clock := k } S' Nd' :=
    ⟨(tablesTyped_with_locals post L k S').2 hT', hJ', hF', hNH', hndisj', hws'⟩
  have hwo_eq : worldOwned { post with locals := L, clock := k } S' Nd' = worldOwned post S' Nd' := rfl
  exact ⟨S', Nd', hsub, hWT'', by rw [hwo_eq]; exact hOG, hFO, trivial⟩

theorem WorldStepSc.of_pre_locals_clock {F : Type}
    {B : BufList} {gw : List String} {keep : List (String × List Nat)}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    {L : HolFiniteMapExact MlS (ValueHOL 64)} {k : Nat}
    (h : WorldStepSc (bufRegions B) gw keep NoExtra { s with locals := L, clock := k } r post) :
    WorldStepSc (bufRegions B) gw keep NoExtra s r post := by
  obtain ⟨⟨hAp, hhp, hG, hK, hW⟩, hsc⟩ := h
  refine ⟨⟨hAp, hhp, hG, hK, fun S Nd hWT hD => ?_⟩, hsc⟩
  obtain ⟨hT, hJ, hF, hNH, hndisj, hws⟩ := hWT
  have hWT' : WorldTypedWith { s with locals := L, clock := k } S Nd :=
    ⟨(tablesTyped_with_locals s L k S).2 hT, hJ, hF, hNH, hndisj, hws⟩
  exact hW S Nd hWT' hD

theorem WorldStepSc.from_entry {F : Type}
    {B : BufList} {gw : List String} {keep : List (String × List Nat)}
    {s post : PanSemStateFiniteExact 64 F} {r r' : Option (PanSemResultExact 64)}
    {callee L : HolFiniteMapExact MlS (ValueHOL 64)} {k : Nat}
    (h : WorldStepSc (bufRegions B) gw keep NoExtra (callEntryStateHOLFinite s callee) r post) :
    WorldStepSc (bufRegions B) gw keep NoExtra s r' { post with locals := L, clock := k } :=
  (WorldStepSc.of_pre_locals_clock h).with_locals_clock (r' := r') L k

theorem WorldStepSc.worldOK_bufs {F : Type}
    {B : BufList} {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (hB : ValidBufList B) (hs : WorldOK s)
    (h : WorldStepSc (bufRegions B) gw keep Q s r post) :
    WorldOK post := by
  obtain ⟨_, S, hS⟩ := hs
  obtain ⟨Nd, hWT⟩ := (worldTyped_iff_with s S).1 hS
  exact h.1.worldOK ⟨S, Nd, hWT, validBufList_disj hB hWT⟩

theorem WorldStepSc.mono_bufs {F : Type}
    {B1 B2 : BufList} {gw1 gw2 : List String}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (hB : ∀ p ∈ B1, p ∈ B2)
    (hgw : ∀ g ∈ gw1, g ∈ gw2)
    (h : WorldStepSc (bufRegions B1) gw1 stdKeep NoExtra s r post) :
    WorldStepSc (bufRegions B2) gw2 stdKeep NoExtra s r post := by
  obtain ⟨⟨hAp, hhp, hG, hK, hW⟩, hsc⟩ := h
  have hsubR : ∀ i ∈ bufRegions B1 s, i ∈ bufRegions B2 s := by
    intro i hi
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hi
    exact List.mem_map.2 ⟨p, hB p hp, rfl⟩
  refine ⟨⟨hAp, hhp, ?_, ?_, ?_⟩, hsc⟩
  · intro k hk
    apply hG k
    intro hm
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hm
    exact hk (List.mem_map.2 ⟨g, hgw g hg, rfl⟩)
  · intro rec hrec hnz k hk hno
    exact hK rec hrec hnz k hk (fun i hi => hno i (hsubR i hi))
  · intro S Nd hWT hD
    have hD1 : IvlsDisj (bufRegions B1 s) (worldTypedIvls s S Nd) :=
      fun i hi j hj => hD i (hsubR i hi) j hj
    obtain ⟨S', Nd', hsub, hWT', hOG, hFO, _⟩ := hW S Nd hWT hD1
    refine ⟨S', Nd', hsub, hWT', hOG, ?_, trivial⟩
    intro a ha hhf
    apply hFO a _ hhf
    intro i hi
    rcases List.mem_append.1 hi with hi1 | hfg
    · rcases List.mem_append.1 hi1 with hwo | hR1
      · exact ha i (List.mem_append_left _ (List.mem_append_left _ hwo))
      · exact ha i (List.mem_append_left _ (List.mem_append_right _ (hsubR i hR1)))
    · exact ha i (List.mem_append_right _ hfg)

theorem WorldStepSc.trans {F : Type}
    {B : BufList} {gw : List String}
    {s1 s2 s3 : PanSemStateFiniteExact 64 F}
    {r1 r2 : Option (PanSemResultExact 64)}
    (hB : ValidBufList B) (hgw : SafeStepGlobals gw)
    (h12 : WorldStepSc (bufRegions B) gw stdKeep NoExtra s1 r1 s2)
    (h23 : WorldStepSc (bufRegions B) gw stdKeep NoExtra s2 r2 s3) :
    WorldStepSc (bufRegions B) gw stdKeep NoExtra s1 r2 s3 := by
  obtain ⟨⟨hA2, hhp12, hG12, hK12, hW12⟩, hsc12⟩ := h12
  obtain ⟨⟨hA3, hhp23, hG23, hK23, hW23⟩, hsc23⟩ := h23
  have hbuf21 : bufRegions B s2 = bufRegions B s1 := bufRegions_eq_of_safeGlobals hB hgw hG12
  have hfmp21 : globN s2 "frame_mem_ptr" = globN s1 "frame_mem_ptr" :=
    globN_eq_of_lookup (hG12 (ofString "frame_mem_ptr") (hgw.not_mem_map (by decide)))
  refine ⟨⟨hA3, le_trans hhp12 hhp23,
    fun k hk => (hG12 k hk).trans (hG23 k hk), ?_, ?_⟩, le_trans hsc23 hsc12⟩
  · intro rec hrec hnz k hk hno
    have hrec_not : ofString rec.1 ∉ (["heap_ptr", "scratch_ptr", "journal_n"] : List String).map ofString := by
      simp only [stdKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
      rcases hrec with rfl | rfl | rfl | rfl <;> decide
    have hg_rec : globN s2 rec.1 = globN s1 rec.1 :=
      globN_eq_of_lookup (hG12 (ofString rec.1) (hgw.not_mem_map hrec_not))
    have h2 : memW s3 (globN s2 rec.1 + k) = memW s2 (globN s2 rec.1 + k) :=
      hK23 rec hrec (by rw [hg_rec]; exact hnz) k hk
        (by change ∀ i ∈ bufRegions B s2, ¬ CellHits (globN s2 rec.1 + k) i
            rw [hbuf21, hg_rec]; exact hno)
    rw [hg_rec] at h2
    exact h2.trans (hK12 rec hrec hnz k hk hno)
  · intro S Nd hWT1 hD1
    obtain ⟨S2, Nd2, hsub12, hWT2, hOG12, hFO12, _⟩ := hW12 S Nd hWT1 hD1
    have hD2 : IvlsDisj (bufRegions B s2) (worldTypedIvls s2 S2 Nd2) := validBufList_disj hB hWT2
    obtain ⟨S3, Nd3, hsub23, hWT3, hOG23, hFO23, _⟩ := hW23 S2 Nd2 hWT2 hD2
    refine ⟨S3, Nd3, fun t ht => hsub23 t (hsub12 t ht), hWT3, ?_, ?_, trivial⟩
    · intro o ho
      rcases hOG23 o ho with rfl | ⟨j, hj, hin_oj⟩ | hin_o23
      · exact Or.inl rfl
      · rcases hOG12 j hj with rfl | ⟨k, hk, hin_jk⟩ | hin_j12
        · left
          rcases o with ⟨o1, o2⟩
          dsimp only [Inside] at hin_oj
          have ho1 : o1 = 0 := by omega
          have ho2 : o2 = 0 := by omega
          rw [ho1, ho2]
        · exact Or.inr (Or.inl ⟨k, hk, le_trans hin_jk.1 hin_oj.1, le_trans hin_oj.2 hin_jk.2⟩)
        · exact Or.inr (Or.inr ⟨le_trans hin_j12.1 hin_oj.1,
            le_trans hin_oj.2 (le_trans hin_j12.2 hhp23)⟩)
      · exact Or.inr (Or.inr ⟨le_trans hhp12 hin_o23.1, hin_o23.2⟩)
    · intro a ha hhf
      have hm12 : s2.memory a = s1.memory a := hFO12 a ha hhf
      have hm23 : s3.memory a = s2.memory a := by
        apply hFO23 a
        · intro i hi hch
          obtain ⟨hc1, hc2⟩ := hch
          rcases List.mem_append.1 hi with hi1 | hfg2
          · rcases List.mem_append.1 hi1 with hwo2 | hR2
            · rcases hOG12 i hwo2 with rfl | ⟨k, hk, hin_ik⟩ | hin_i12
              · dsimp only at hc2; omega
              · exact ha k (List.mem_append_left _ (List.mem_append_left _ hk))
                  ⟨by dsimp only [Inside] at hin_ik; omega,
                   by dsimp only [Inside] at hin_ik; omega⟩
              · have hp2_lim : globN s2 "heap_ptr" ≤ heapLimit := hA2.2.2.1
                exact hhf ⟨by unfold heapFree; dsimp only [Inside] at hin_i12 ⊢; omega,
                           by unfold heapFree; dsimp only [Inside] at hin_i12 ⊢; omega⟩
            · change i ∈ bufRegions B s2 at hR2
              rw [hbuf21] at hR2
              exact ha i (List.mem_append_left _ (List.mem_append_right _ hR2)) ⟨hc1, hc2⟩
          · simp only [List.mem_singleton] at hfg2
            subst hfg2
            exact ha (freeGap s1) (List.mem_append_right _ (List.mem_singleton.2 rfl))
              ⟨by unfold freeGap at hc1 ⊢; dsimp only at hc1 ⊢; omega,
               by unfold freeGap at hc2 ⊢; dsimp only at hc2 ⊢; omega⟩
        · intro ⟨hc1, hc2⟩
          have hp2_lim : globN s2 "heap_ptr" ≤ heapLimit := hA2.2.2.1
          exact hhf ⟨by unfold heapFree at hc1 hc2 ⊢; dsimp only at hc1 hc2 ⊢; omega,
                     by unfold heapFree at hc1 hc2 ⊢; dsimp only at hc1 hc2 ⊢; omega⟩
      exact hm23.trans hm12

/-! ## 2. `FlowingOrResumes` and `ProgWStep` Control-Flow Combinators -/

def FlowingOrResumes (r : Option (PanSemResultExact 64)) : Prop :=
  r = none ∨ r = some .continue ∨ r = some .break ∨ Resumes r

theorem not_flowingOrResumes_error : ¬ FlowingOrResumes (some .error) := by
  rintro (h | h | h | ⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h

theorem not_flowingOrResumes_finalFfi {ev} : ¬ FlowingOrResumes (some (.finalFfi ev)) := by
  rintro (h | h | h | ⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h

def ProgWStep (B : BufList) (gw : List String) (prog : ProgHOL 64) : Prop :=
  ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
    s.code = originalRuntimeCode → WorldOK s →
    (evaluateHOLFiniteState s prog).1 ≠ some .timeOut →
    FlowingOrResumes (evaluateHOLFiniteState s prog).1 →
    WorldStepSc (bufRegions B) gw stdKeep NoExtra
      s (evaluateHOLFiniteState s prog).1 (evaluateHOLFiniteState s prog).2

theorem progWStep_mono {B1 B2 : BufList} {gw1 gw2 : List String} {prog : ProgHOL 64}
    (hB : ∀ p ∈ B1, p ∈ B2) (hgw : ∀ g ∈ gw1, g ∈ gw2)
    (h : ProgWStep B1 gw1 prog) : ProgWStep B2 gw2 prog :=
  fun s hc hW hnt hfr => (h s hc hW hnt hfr).mono_bufs hB hgw

theorem progWStep_skip (B : BufList) (gw : List String) : ProgWStep B gw .skip := by
  intro F s _ hW _ _
  rw [evaluateHOLFiniteState_skip]
  exact WorldStepSc.refl s none hW.1

theorem progWStep_continue (B : BufList) (gw : List String) : ProgWStep B gw .continue := by
  intro F s _ hW _ _
  rw [evaluateHOLFiniteState_continue]
  exact WorldStepSc.refl s (some .continue) hW.1

theorem progWStep_break (B : BufList) (gw : List String) : ProgWStep B gw .break := by
  intro F s _ hW _ _
  rw [evaluateHOLFiniteState_break]
  exact WorldStepSc.refl s (some .break) hW.1

theorem progWStep_return (B : BufList) (gw : List String) (e : ExpHOL 64) :
    ProgWStep B gw (.return e) := by
  intro F s _ hW _ hfr
  rw [evaluateHOLFiniteState_return] at hfr ⊢
  rcases hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e with _ | v
  · simp [hev] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [hev] at hfr ⊢
    split
    · exact (WorldStepSc.refl s none hW.1).with_locals_clock _ s.clock
    · rename_i hbad; simp [hbad] at hfr; exact absurd hfr not_flowingOrResumes_error

theorem progWStep_raise (B : BufList) (gw : List String) (eid : MlS) (e : ExpHOL 64) :
    ProgWStep B gw (.raise eid e) := by
  intro F s _ hW _ hfr
  rw [evaluateHOLFiniteState_raise] at hfr ⊢
  rcases hsh : s.eshapes.lookup eid with _ | sh
  · simp [hsh] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [hsh] at hfr ⊢
    rcases hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e with _ | v
    · simp [hev] at hfr; exact absurd hfr not_flowingOrResumes_error
    · simp only [hev] at hfr ⊢
      split
      · exact (WorldStepSc.refl s none hW.1).with_locals_clock _ s.clock
      · rename_i hbad; simp [hbad] at hfr; exact absurd hfr not_flowingOrResumes_error

theorem progWStep_assign_local (B : BufList) (gw : List String) (x : MlS) (e : ExpHOL 64) :
    ProgWStep B gw (.assign .local x e) := by
  intro F s _ hW _ hfr
  rw [evaluateHOLFiniteState_assign] at hfr ⊢
  rcases hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e with _ | v
  · simp [hev] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [hev] at hfr ⊢
    by_cases hv : s.isValidValueHOLFinite .local x v = true
    · rw [if_pos hv]
      exact (WorldStepSc.refl s none hW.1).with_locals_clock _ s.clock
    · rw [if_neg hv] at hfr; exact absurd hfr not_flowingOrResumes_error

theorem progWStep_dec {B : BufList} {gw : List String} {x : MlS} {sh : ShapeHOL} {e : ExpHOL 64}
    {body : ProgHOL 64} (hb : ProgWStep B gw body) :
    ProgWStep B gw (.dec x sh e body) := by
  intro F s hc hW hnt hfr
  rw [evaluateHOLFiniteState_dec_total] at hnt hfr ⊢
  rcases hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e with _ | val
  · simp [hev] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [hev] at hnt hfr ⊢
    by_cases hok : shapeEqHOL sh (shapeOfHOLExact val) = true
    · simp only [hok, ↓reduceIte] at hnt hfr ⊢
      set s1 := setVarHOLFinite x val s
      have hW1 : WorldOK s1 := localsFree_worldOK s _ s.clock hW
      have hstep := hb s1 hc hW1 hnt hfr
      exact (WorldStepSc.of_pre_locals_clock hstep).with_locals_clock _ (evaluateHOLFiniteState s1 body).2.clock
    · simp [hok] at hfr; exact absurd hfr not_flowingOrResumes_error

theorem progWStep_ite {B : BufList} {gw : List String} {cond : ExpHOL 64} {yes no : ProgHOL 64}
    (hy : ProgWStep B gw yes) (hn : ProgWStep B gw no) :
    ProgWStep B gw (.ite cond yes no) := by
  intro F s hc hW hnt hfr
  rw [evaluateHOLFiniteState_ite] at hnt hfr ⊢
  rcases hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond with _ | cv
  · simp [hev] at hfr; exact absurd hfr not_flowingOrResumes_error
  · rcases cv with ⟨⟨w⟩⟩ | _ | _
    · simp only [hev] at hnt hfr ⊢
      by_cases hw : w = 0
      · simp only [hw, ↓reduceIte] at hnt hfr ⊢; exact hn s hc hW hnt hfr
      · simp only [hw, ↓reduceIte] at hnt hfr ⊢; exact hy s hc hW hnt hfr
    · simp [hev] at hfr; exact absurd hfr not_flowingOrResumes_error
    · simp [hev] at hfr; exact absurd hfr not_flowingOrResumes_error

theorem progWStep_seq {B : BufList} {gw : List String} {p1 p2 : ProgHOL 64}
    (hB : ValidBufList B) (hgw : SafeStepGlobals gw)
    (h1 : ProgWStep B gw p1) (h2 : ProgWStep B gw p2) :
    ProgWStep B gw (.seq p1 p2) := by
  intro F s hc hW hnt hfr
  have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata s p1).1
  rw [evaluateHOLFiniteState_seq_line780] at hnt hfr ⊢
  rcases hr1 : evaluateHOLFiniteState s p1 with ⟨r1, mid⟩
  simp only [hr1] at hmeta hnt hfr ⊢
  cases r1 with
  | none =>
    have hs1 := h1 s hc hW (by rw [hr1]; simp) (by rw [hr1]; exact Or.inl rfl)
    rw [hr1] at hs1; dsimp only at hs1
    have hW_mid : WorldOK mid := hs1.worldOK_bufs hB hW
    have hs2 := h2 mid (hmeta.trans hc) hW_mid hnt hfr
    exact WorldStepSc.trans hB hgw hs1 hs2
  | some r =>
    have hs1 := h1 s hc hW (by rw [hr1]; exact hnt) (by rw [hr1]; exact hfr)
    rw [hr1] at hs1
    exact hs1

theorem progWStep_while {B : BufList} {gw : List String} {cond : ExpHOL 64} {body : ProgHOL 64}
    (hB : ValidBufList B) (hgw : SafeStepGlobals gw)
    (hb : ProgWStep B gw body) :
    ProgWStep B gw (.while cond body) := by
  intro F s0 hc0 hW0 hnt0 hfr0
  suffices ∀ (k : Nat) (s : PanSemStateFiniteExact 64 F),
      s.clock = k → s.code = originalRuntimeCode → WorldOK s →
      (evaluateHOLFiniteState s (.while cond body)).1 ≠ some .timeOut →
      FlowingOrResumes (evaluateHOLFiniteState s (.while cond body)).1 →
      WorldStepSc (bufRegions B) gw stdKeep NoExtra
        s (evaluateHOLFiniteState s (.while cond body)).1
        (evaluateHOLFiniteState s (.while cond body)).2 from
    this s0.clock s0 rfl hc0 hW0 hnt0 hfr0
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro s hclk hc hW hnt hfr
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt hfr ⊢
    rcases hev : @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a)) cond with
      _ | cv
    · simp only [hev] at hfr; exact absurd hfr not_flowingOrResumes_error
    · simp only [hev] at hnt hfr ⊢
      rcases cv with ⟨⟨w⟩⟩ | _ | _
      · dsimp only at hnt hfr ⊢
        by_cases hw : w = 0
        · subst hw; exact WorldStepSc.refl s none hW.1
        · rw [if_pos hw] at hnt hfr ⊢
          by_cases hk0 : s.clock = 0
          · simp [hk0] at hnt
          · rw [if_neg hk0] at hnt hfr ⊢
            set sd := decClockHOLFinite s
            have hWd : WorldOK sd := localsFree_worldOK s s.locals (s.clock - 1) hW
            have hclk_le := evaluateHOLFiniteState_clock_le sd body
            have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata sd body).1
            rcases hbo : evaluateHOLFiniteState sd body with ⟨rb, mid⟩
            have hbo' : evaluateHOLFiniteState (decClockHOLFinite s) body = (rb, mid) := hbo
            simp only [sd, hbo'] at hnt hfr hclk_le hmeta ⊢
            have hmid_lt : mid.clock < k := by
              change mid.clock ≤ s.clock - 1 at hclk_le; omega
            have hnt_b : (evaluateHOLFiniteState sd body).1 ≠ some .timeOut := by
              rw [hbo]; rintro rfl; exact hnt rfl
            cases rb with
            | none =>
              have hsb := hb sd hc hWd hnt_b (by rw [hbo]; exact Or.inl rfl)
              rw [hbo] at hsb
              have hW_mid : WorldOK mid := hsb.worldOK_bufs hB hWd
              have hsb' : WorldStepSc (bufRegions B) gw stdKeep NoExtra s none mid :=
                (WorldStepSc.of_pre_locals_clock hsb).with_locals_clock mid.locals mid.clock
              have htail := ih mid.clock hmid_lt mid rfl (hmeta.trans hc) hW_mid hnt hfr
              exact WorldStepSc.trans hB hgw hsb' htail
            | some r =>
              cases r with
              | «continue» =>
                have hsb := hb sd hc hWd hnt_b (by rw [hbo]; exact Or.inr (Or.inl rfl))
                rw [hbo] at hsb
                have hW_mid : WorldOK mid := hsb.worldOK_bufs hB hWd
                have hsb' : WorldStepSc (bufRegions B) gw stdKeep NoExtra s (some .continue) mid :=
                  (WorldStepSc.of_pre_locals_clock hsb).with_locals_clock mid.locals mid.clock
                have htail := ih mid.clock hmid_lt mid rfl (hmeta.trans hc) hW_mid hnt hfr
                exact WorldStepSc.trans hB hgw hsb' htail
              | «break» =>
                have hsb := hb sd hc hWd hnt_b (by rw [hbo]; exact Or.inr (Or.inr (Or.inl rfl)))
                rw [hbo] at hsb
                exact (WorldStepSc.of_pre_locals_clock hsb).with_locals_clock mid.locals mid.clock
              | timeOut => exact absurd rfl hnt
              | error => exact absurd hfr not_flowingOrResumes_error
              | finalFfi _ => exact absurd hfr not_flowingOrResumes_finalFfi
              | returned v =>
                have hsb := hb sd hc hWd hnt_b (by rw [hbo]; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨v, rfl⟩))))
                rw [hbo] at hsb
                exact (WorldStepSc.of_pre_locals_clock hsb).with_locals_clock mid.locals mid.clock
              | exception eid ev =>
                have hres_ex : Resumes (some (.exception eid ev)) := by
                  rcases hfr with h | h | h | hr <;> try simp at h
                  exact hr
                have hsb := hb sd hc hWd hnt_b (by rw [hbo]; exact Or.inr (Or.inr (Or.inr hres_ex)))
                rw [hbo] at hsb
                exact (WorldStepSc.of_pre_locals_clock hsb).with_locals_clock mid.locals mid.clock
      · exact absurd hfr not_flowingOrResumes_error
      · exact absurd hfr not_flowingOrResumes_error

theorem progWStep_call0 {B Bf : BufList} {gw gwf : List String} {fname : MlS}
    {args : List (ExpHOL 64)}
    (hB : ∀ p ∈ Bf, p ∈ B) (hgw : ∀ g ∈ gwf, g ∈ gw)
    (hf : WorldKeepsSc WorldOK (bufRegions Bf) gwf stdKeep NoExtra fname) :
    ProgWStep B gw (.call (some (none, none)) fname args) := by
  intro F s hc hW hnt hfr
  rw [evaluateHOLFiniteState_call] at hnt hfr ⊢
  rcases hargs : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vs
  · simp [evalListHOLFinite, hargs] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [evalListHOLFinite, hargs] at hnt hfr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vs with _ | ⟨body', callee, ret'⟩
    · simp [hl] at hfr; exact absurd hfr not_flowingOrResumes_error
    · simp only [hl] at hnt hfr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · rw [if_neg hz] at hnt hfr ⊢
        let ent := callEntryStateHOLFinite s callee
        have hWent : WorldOK ent := localsFree_worldOK s callee (s.clock - 1) hW
        rcases hrun : evaluateHOLFiniteState ent body' with ⟨res, cpost⟩
        simp only [ent] at hrun
        simp only [hrun] at hnt hfr ⊢
        have hnt_c : (evaluateHOLFiniteState ent body').1 ≠ some .timeOut := by
          simp only [ent, hrun]; rintro rfl; simp at hnt
        cases res with
        | none => exact absurd hfr not_flowingOrResumes_error
        | some cr =>
          cases cr with
          | timeOut => simp at hnt
          | error | «break» | «continue» => exact absurd hfr not_flowingOrResumes_error
          | finalFfi _ => exact absurd hfr not_flowingOrResumes_finalFfi
          | returned v =>
            dsimp only at hfr ⊢
            split
            · have hspec := FunSpec.at_lookup hf s hc vs body' callee ret' hl hWent hnt_c
              simp only [ent, hrun] at hspec
              have hstep := (hspec (Or.inl ⟨v, rfl⟩)).mono_bufs hB hgw
              exact hstep.from_entry
            · rename_i hbad; simp [hbad] at hfr; exact absurd hfr not_flowingOrResumes_error
          | exception eid ev =>
            dsimp only at hfr ⊢
            have hres_ex : Resumes (some (.exception eid ev)) := by
              rcases hfr with h | h | h | hr <;> try simp at h
              exact hr
            have hspec := FunSpec.at_lookup hf s hc vs body' callee ret' hl hWent hnt_c
            simp only [ent, hrun] at hspec
            have hstep := (hspec hres_ex).mono_bufs hB hgw
            exact hstep.from_entry

theorem progWStep_call_local {B Bf : BufList} {gw gwf : List String} {x fname : MlS}
    {args : List (ExpHOL 64)}
    (hB : ∀ p ∈ Bf, p ∈ B) (hgw : ∀ g ∈ gwf, g ∈ gw)
    (hf : WorldKeepsSc WorldOK (bufRegions Bf) gwf stdKeep NoExtra fname) :
    ProgWStep B gw (.call (some (some (.local, x), none)) fname args) := by
  intro F s hc hW hnt hfr
  rw [evaluateHOLFiniteState_call] at hnt hfr ⊢
  rcases hargs : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vs
  · simp [evalListHOLFinite, hargs] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [evalListHOLFinite, hargs] at hnt hfr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vs with _ | ⟨body', callee, ret'⟩
    · simp [hl] at hfr; exact absurd hfr not_flowingOrResumes_error
    · simp only [hl] at hnt hfr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · rw [if_neg hz] at hnt hfr ⊢
        let ent := callEntryStateHOLFinite s callee
        have hWent : WorldOK ent := localsFree_worldOK s callee (s.clock - 1) hW
        rcases hrun : evaluateHOLFiniteState ent body' with ⟨res, cpost⟩
        simp only [ent] at hrun
        simp only [hrun] at hnt hfr ⊢
        have hnt_c : (evaluateHOLFiniteState ent body').1 ≠ some .timeOut := by
          simp only [ent, hrun]; rintro rfl; simp at hnt
        cases res with
        | none => exact absurd hfr not_flowingOrResumes_error
        | some cr =>
          cases cr with
          | timeOut => simp at hnt
          | error | «break» | «continue» => exact absurd hfr not_flowingOrResumes_error
          | finalFfi _ => exact absurd hfr not_flowingOrResumes_finalFfi
          | returned v =>
            dsimp only at hfr ⊢
            split
            · split
              · have hspec := FunSpec.at_lookup hf s hc vs body' callee ret' hl hWent hnt_c
                simp only [ent, hrun] at hspec
                have hstep := (hspec (Or.inl ⟨v, rfl⟩)).mono_bufs hB hgw
                exact hstep.from_entry
              · rename_i hb2; simp [‹shapeEqHOL _ _ = true›, hb2] at hfr; exact absurd hfr not_flowingOrResumes_error
            · rename_i hb1; simp [hb1] at hfr; exact absurd hfr not_flowingOrResumes_error
          | exception eid ev =>
            dsimp only at hfr ⊢
            have hres_ex : Resumes (some (.exception eid ev)) := by
              rcases hfr with h | h | h | hr <;> try simp at h
              exact hr
            have hspec := FunSpec.at_lookup hf s hc vs body' callee ret' hl hWent hnt_c
            simp only [ent, hrun] at hspec
            have hstep := (hspec hres_ex).mono_bufs hB hgw
            exact hstep.from_entry

theorem progWStep_decCall {B Bf : BufList} {gw gwf : List String}
    {x : MlS} {sh : ShapeHOL} {fname : MlS} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hBvalid : ValidBufList B) (hgwSafe : SafeStepGlobals gw)
    (hB : ∀ p ∈ Bf, p ∈ B) (hgw : ∀ g ∈ gwf, g ∈ gw)
    (hf : WorldKeepsSc WorldOK (bufRegions Bf) gwf stdKeep NoExtra fname)
    (hcont : ProgWStep B gw cont) :
    ProgWStep B gw (.decCall x sh fname args cont) := by
  intro F s hc hW hnt hfr
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hfr ⊢
  rcases hargs : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vs
  · simp [evalListHOLFinite, hargs] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [evalListHOLFinite, hargs] at hnt hfr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vs with _ | ⟨body', callee, ret'⟩
    · simp [hl] at hfr; exact absurd hfr not_flowingOrResumes_error
    · simp only [hl] at hnt hfr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · rw [if_neg hz] at hnt hfr ⊢
        let ent := callEntryStateHOLFinite s callee
        have hWent : WorldOK ent := localsFree_worldOK s callee (s.clock - 1) hW
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata ent body').1
        rcases hrun : evaluateHOLFiniteState ent body' with ⟨res, cpost⟩
        simp only [ent] at hrun hmeta
        simp only [hrun] at hmeta hnt hfr ⊢
        have hnt_c : (evaluateHOLFiniteState ent body').1 ≠ some .timeOut := by
          simp only [ent, hrun]; rintro rfl; simp at hnt
        cases res with
        | none => exact absurd hfr not_flowingOrResumes_error
        | some cr =>
          cases cr with
          | timeOut => simp at hnt
          | error | «break» | «continue» => exact absurd hfr not_flowingOrResumes_error
          | finalFfi _ => exact absurd hfr not_flowingOrResumes_finalFfi
          | returned v =>
            dsimp only at hnt hfr ⊢
            by_cases hsh : (shapeEqHOL (shapeOfHOLExact v) sh && shapeEqHOL (shapeOfHOLExact v) ret') = true
            · simp only [hsh, ↓reduceIte] at hnt hfr ⊢
              have hspec := FunSpec.at_lookup hf s hc vs body' callee ret' hl hWent hnt_c
              simp only [ent, hrun] at hspec
              have hstep1 := (hspec (Or.inl ⟨v, rfl⟩)).mono_bufs hB hgw
              set s1 := setVarHOLFinite x v { cpost with locals := s.locals }
              have hs1_step : WorldStepSc (bufRegions B) gw stdKeep NoExtra s none s1 :=
                hstep1.from_entry
              have hWs1 : WorldOK s1 := hs1_step.worldOK_bufs hBvalid hW
              have hs1_code : s1.code = originalRuntimeCode := hmeta.trans hc
              have hstep2 := hcont s1 hs1_code hWs1 hnt hfr
              have hstep2' := hstep2.with_locals_clock (r' := (evaluateHOLFiniteState s1 cont).1)
                (HolFiniteMapExact.resVarEq (evaluateHOLFiniteState s1 cont).2.locals (x, s.locals.lookup x))
                (evaluateHOLFiniteState s1 cont).2.clock
              exact WorldStepSc.trans hBvalid hgwSafe hs1_step hstep2'
            · simp [hsh] at hfr; exact absurd hfr not_flowingOrResumes_error
          | exception eid ev =>
            dsimp only at hfr ⊢
            have hres_ex : Resumes (some (.exception eid ev)) := by
              rcases hfr with h | h | h | hr <;> try simp at h
              exact hr
            have hspec := FunSpec.at_lookup hf s hc vs body' callee ret' hl hWent hnt_c
            simp only [ent, hrun] at hspec
            have hstep := (hspec hres_ex).mono_bufs hB hgw
            exact hstep.from_entry

theorem worldKeepsSc_of_progWStep {B : BufList} {gw : List String}
    {fname : MlS} {params : List (MlS × ShapeHOL)} {body : ProgHOL 64} {ret : ShapeHOL}
    (hlook : originalRuntimeCode.lookup fname = some (params, body, ret))
    (hp : ProgWStep B gw body) :
    WorldKeepsSc WorldOK (bufRegions B) gw stdKeep NoExtra fname :=
  ⟨params, body, ret, hlook, fun s hc hW _ hnt hres =>
    hp s hc hW hnt (Or.inr (Or.inr (Or.inr hres)))⟩

theorem worldKeepsSc_of_readOnly {fname : MlS} (hro : ReadOnlyFn fname) :
    WorldKeepsSc WorldOK (bufRegions []) [] stdKeep NoExtra fname := by
  obtain ⟨ps, body, ret, hl, hb⟩ := hro
  refine ⟨ps, body, ret, hl, fun s hc hW hex hnt hres => ?_⟩
  have heq := hb s hc hW.1.1 hex hnt hres
  set post := (evaluateHOLFiniteState s body).2
  have h0 : WorldStepSc (bufRegions []) [] stdKeep NoExtra s (evaluateHOLFiniteState s body).1
      { s with locals := post.locals, clock := post.clock } :=
    (WorldStepSc.refl s none hW.1).with_locals_clock post.locals post.clock
  rwa [← heq] at h0

theorem worldKeepsSc_sk_make :
    WorldKeepsSc WorldOK (bufRegions [("sk_buf", 52)]) [] stdKeep NoExtra (ofString "sk_make") := by
  obtain ⟨ps, body, ret, hl, hb⟩ := EvmFrameSpecs.wk_sk_make
  refine ⟨ps, body, ret, hl, fun s hc hW hex hnt hres => ?_⟩
  have hstep := hb s hc hW hex hnt hres
  have hsp_eq : globN (evaluateHOLFiniteState s body).2 "scratch_ptr" = globN s "scratch_ptr" :=
    globN_eq_of_lookup (hstep.2.2.1 (ofString "scratch_ptr") (by decide))
  exact ⟨hstep, by rw [hsp_eq]⟩

/-! ## 3. `noCatchableRaise` for `htab_*`, `alloc`, `memcpy`, `memzero`, `jset`, `jdel` -/

def noCatchableRaise (good : MlS → Bool) : ProgHOL 64 → Bool
  | .dec _ _ _ b => noCatchableRaise good b
  | .seq a b => noCatchableRaise good a && noCatchableRaise good b
  | .ite _ a b => noCatchableRaise good a && noCatchableRaise good b
  | .while _ b => noCatchableRaise good b
  | .decCall _ _ f _ cont => good f && noCatchableRaise good cont
  | .call (some (_, none)) f _ => good f
  | .raise eid _ => eid == ofString "TrapErr"
  | .skip | .break | .continue | .annot _ _ | .return _
  | .assign _ _ _ | .store _ _ | .storeByte _ _ | .store32 _ _
  | .shMemStore _ _ _ | .extCall _ _ _ _ _ | .primitive _ _ _ => true
  | _ => false

private theorem lex_ncr {a1 a2 b1 b2 : Nat} (h : a1 < a2 ∨ a1 = a2 ∧ b1 < b2) :
    Prod.Lex (· < ·) (· < ·) (a1, b1) (a2, b2) := by
  rcases h with h | ⟨rfl, h⟩
  · exact Prod.Lex.left _ _ h
  · exact Prod.Lex.right _ h

theorem evaluate_noCatchableRaise {F : Type} (good : MlS → Bool)
    (hgood : ∀ f, good f = true → ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup f values =
        some (body, callee, rs) →
      noCatchableRaise good body = true)
    (p : ProgHOL 64) (hp : noCatchableRaise good p = true)
    (s : PanSemStateFiniteExact 64 F) (hcode : s.code = originalRuntimeCode) :
    ∀ eid v, eid ≠ ofString "TrapErr" → (evaluateHOLFiniteState s p).1 ≠ some (.exception eid v) := by
  cases shape : p with
  | tick => simp [shape, noCatchableRaise] at hp
  | skip => rw [evaluateHOLFiniteState_skip]; simp
  | «break» => rw [evaluateHOLFiniteState_break]; simp
  | «continue» => rw [evaluateHOLFiniteState_continue]; simp
  | annot _ _ => rw [evaluateHOLFiniteState_annot]; simp
  | «return» _ =>
    rw [evaluateHOLFiniteState_return]; split <;> [simp; (split <;> simp)]
  | assign _ _ _ =>
    rw [evaluateHOLFiniteState_assign]; split <;> [simp; (split <;> simp)]
  | store _ _ =>
    rw [evaluateHOLFiniteState_store]; split <;> [(split <;> [(split <;> simp); simp]); simp]
  | storeByte _ _ =>
    rw [evaluateHOLFiniteState_storeByte]; split <;> [(split <;> [(split <;> simp); simp]); simp]
  | store32 _ _ =>
    rw [evaluateHOLFiniteState_store32]; split <;> [(split <;> [(split <;> simp); simp]); simp]
  | shMemStore _ _ _ =>
    rw [evaluateHOLFiniteState_shMemStore_total]; dsimp only
    split
    · unfold shMemStoreHOLExact
      split <;> split
      all_goals simp [ofExact, toExact]
      all_goals split <;> simp
    · simp
  | shMemLoad _ _ _ _ => simp [shape, noCatchableRaise] at hp
  | extCall _ _ _ _ _ =>
    rw [evaluateHOLFiniteState_extCall_source]
    split <;> [ (split <;> [ (split <;> simp); simp ]); simp ]
  | primitive _ _ _ =>
    rw [evaluateHOLFiniteState_primitive]; split <;> [simp; (split <;> [simp; (split <;> simp)])]
  | raise name _ =>
    have htrap : name = ofString "TrapErr" := by
      simpa [shape, noCatchableRaise, beq_iff_eq] using hp
    subst htrap
    intro eid v hne
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split <;> [simp [hne.symm]; simp]
    · simp
  | dec name _ _ body =>
    have hb : noCatchableRaise good body = true := by simpa [shape, noCatchableRaise] using hp
    rw [evaluateHOLFiniteState_dec_total]; dsimp only
    split
    · simp
    · rename_i val _
      split
      · exact evaluate_noCatchableRaise good hgood body hb (setVarHOLFinite name val s) hcode
      · simp
  | seq a b =>
    have hab : noCatchableRaise good a = true ∧ noCatchableRaise good b = true := by
      simpa [shape, noCatchableRaise, Bool.and_eq_true] using hp
    have ih1 := evaluate_noCatchableRaise good hgood a hab.1 s hcode
    have rem := evaluateHOLFiniteState_clock_le s a
    have meta' := PanRunBounded.evaluateHOLFiniteState_metadata s a
    rw [evaluateHOLFiniteState_seq_line780]
    rcases hr : evaluateHOLFiniteState s a with ⟨r1, mid⟩
    rw [hr] at ih1 rem meta'
    dsimp only at ih1 rem meta' ⊢
    cases r1 with
    | none =>
      have mclock : mid.clock ≤ s.clock := rem
      exact evaluate_noCatchableRaise good hgood b hab.2 mid (meta'.1.trans hcode)
    | some _ => exact ih1
  | ite _ yes no =>
    have hy : noCatchableRaise good yes = true ∧ noCatchableRaise good no = true := by
      simpa [shape, noCatchableRaise, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_noCatchableRaise good hgood no hy.2 s hcode
      · exact evaluate_noCatchableRaise good hgood yes hy.1 s hcode
    · simp
  | «while» cond body =>
    have hb : noCatchableRaise good body = true := by simpa [shape, noCatchableRaise] using hp
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · simp
        · dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have ih1 := evaluate_noCatchableRaise good hgood body hb (decClockHOLFinite s) hcode
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          have meta' := PanRunBounded.evaluateHOLFiniteState_metadata (decClockHOLFinite s) body
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
          rw [hbr] at ih1 rem meta'
          dsimp only at ih1 rem meta' ⊢
          have smaller : mid.clock < s.clock := by change mid.clock ≤ s.clock - 1 at rem; omega
          have mCode : mid.code = originalRuntimeCode := meta'.1.trans hcode
          cases r1 with
          | none =>
            exact evaluate_noCatchableRaise good hgood (.while cond body) (by simpa [noCatchableRaise] using hb) mid mCode
          | some r =>
            cases r with
            | «continue» =>
              exact evaluate_noCatchableRaise good hgood (.while cond body) (by simpa [noCatchableRaise] using hb) mid mCode
            | «break» => simp
            | _ => exact ih1
      · simp
    · simp
  | decCall name _ fn args cont =>
    have hc : good fn = true ∧ noCatchableRaise good cont = true := by
      simpa [shape, noCatchableRaise, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
    rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
    · simp
    · dsimp only
      rcases hl : lookupCodeHOLFinite s.code.lookup fn values with _ | ⟨body, callee, rs⟩
      · simp
      · dsimp only
        have hl' : lookupCodeHOLFinite originalRuntimeCode.lookup fn values = some (body, callee, rs) := by rwa [← hcode]
        have bodyOk := hgood fn hc.1 values body callee rs hl'
        split
        · simp
        · have ih1 := evaluate_noCatchableRaise good hgood body bodyOk (callEntryStateHOLFinite s callee) hcode
          have meta' := PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body
          have cl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite s callee) body
          rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨res, st⟩
          rw [hrun] at ih1 meta' cl
          dsimp only at ih1 meta' cl ⊢
          change st.clock ≤ s.clock - 1 at cl
          have small : st.clock < s.clock := by omega
          have stCode : st.code = originalRuntimeCode := meta'.1.trans hcode
          cases res with
          | none => simp
          | some r =>
            cases r with
            | returned v =>
              dsimp only
              split
              · set resumed := setVarHOLFinite name v { st with locals := s.locals }
                have smallR : resumed.clock < s.clock := small
                have rCode : resumed.code = originalRuntimeCode := stCode
                exact evaluate_noCatchableRaise good hgood cont hc.2 resumed rCode
              · simp
            | «break» => simp
            | «continue» => simp
            | _ => exact ih1
  | call tail fn args =>
    cases tail with
    | none => simp [shape, noCatchableRaise] at hp
    | some th =>
      rcases th with ⟨dst, hdl⟩
      cases hdl with
      | some _ => simp [shape, noCatchableRaise] at hp
      | none =>
        have hf : good fn = true := by simpa [shape, noCatchableRaise] using hp
        rw [evaluateHOLFiniteState_call]
        rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
        · simp
        · dsimp only
          rcases hl : lookupCodeHOLFinite s.code.lookup fn values with _ | ⟨body, callee, rs⟩
          · simp
          · dsimp only
            have hl' : lookupCodeHOLFinite originalRuntimeCode.lookup fn values = some (body, callee, rs) := by rwa [← hcode]
            have bodyOk := hgood fn hf values body callee rs hl'
            split
            · simp
            · have ih1 := evaluate_noCatchableRaise good hgood body bodyOk (callEntryStateHOLFinite s callee) hcode
              have cl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite s callee) body
              rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨res, st⟩
              rw [hrun] at ih1 cl
              dsimp only at ih1 cl ⊢
              change st.clock ≤ s.clock - 1 at cl
              have small : st.clock < s.clock := by omega
              cases res with
              | none => simp
              | some r =>
                cases r with
                | returned rv =>
                  dsimp only
                  split
                  · cases dst with
                    | none => simp
                    | some kv =>
                      rcases kv with ⟨kd, nm⟩
                      dsimp only
                      by_cases hv : isValidValueHOLExact s.toExact kd nm rv = true <;> simp [hv]
                  · simp
                | «break» => simp
                | «continue» => simp
                | exception _ _ => dsimp only; exact ih1
                | timeOut | error | finalFfi _ => dsimp only; exact ih1
termination_by (s.clock, sizeOf p)
decreasing_by
  all_goals
    simp_wf
    apply lex_ncr
    try subst shape
    try simp only [setVarHOLFinite, decClockHOLFinite, callEntryStateHOLFinite, ProgHOL.seq.sizeOf_spec,
      ProgHOL.ite.sizeOf_spec, ProgHOL.dec.sizeOf_spec, ProgHOL.while.sizeOf_spec, ProgHOL.decCall.sizeOf_spec]
    first
      | exact Or.inl small
      | exact Or.inl smaller
      | exact Or.inl smallR
      | exact Or.inl (by omega)
      | (rcases Nat.lt_or_eq_of_le mclock with h | h
         · exact Or.inl h
         · right; refine ⟨h, ?_⟩; simp +arith)
      | (right; refine ⟨rfl, ?_⟩; simp +arith)
      | (right; refine ⟨trivial, ?_⟩; simp +arith)

def trapOnlyCallees (f : MlS) : Bool :=
  f == ofString "trap_with" || f == ofString "alloc" || f == ofString "memcpy" ||
  f == ofString "memzero" || f == ofString "memeq" || f == ofString "htab_new" ||
  f == ofString "htab_find_leaf" || f == ofString "htab_get" || f == ofString "htab_first_diff" ||
  f == ofString "htab_grow" || f == ofString "htab_new_node" ||
  f == ofString "htab_new_internal" || f == ofString "htab_new_leaf" ||
  f == ofString "htab_set" || f == ofString "htab_del" ||
  f == ofString "jset" || f == ofString "jdel"

theorem trapOnlyCallees_good :
    ∀ f, trapOnlyCallees f = true → ∀ values body callee rs,
      lookupCodeHOLFinite originalRuntimeCode.lookup f values = some (body, callee, rs) →
      noCatchableRaise trapOnlyCallees body = true := by
  intro f hf values body callee rs hfound
  obtain ⟨params, rs', hinst⟩ := InitECandidate.Solver.GuestGlobalKeep.lookupCode_installed hfound
  simp only [trapOnlyCallees, Bool.or_eq_true, beq_iff_eq] at hf
  rcases hf with (((((((((((((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl
  · have hl := lookup_of_guestAst_getElem 3 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_trap_with) rfl
    change originalRuntimeCode.lookup (ofString "trap_with") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; decide
  · have hl := lookup_of_guestAst_getElem 7 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_alloc) rfl
    change originalRuntimeCode.lookup (ofString "alloc") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; decide
  · have hl := lookup_of_guestAst_getElem 16 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_memcpy) rfl
    change originalRuntimeCode.lookup (ofString "memcpy") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; decide
  · have hl := lookup_of_guestAst_getElem 17 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_memzero) rfl
    change originalRuntimeCode.lookup (ofString "memzero") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; decide
  · have hl := lookup_of_guestAst_getElem 18 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_memeq) rfl
    change originalRuntimeCode.lookup (ofString "memeq") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; decide
  · have hl := lookup_of_guestAst_getElem 128 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_htab_new) rfl
    change originalRuntimeCode.lookup (ofString "htab_new") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; decide
  · have hl := lookup_of_guestAst_getElem 131 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_htab_find_leaf) rfl
    change originalRuntimeCode.lookup (ofString "htab_find_leaf") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; decide
  · have hl := lookup_of_guestAst_getElem 132 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_htab_get) rfl
    change originalRuntimeCode.lookup (ofString "htab_get") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; decide
  · have hl := lookup_of_guestAst_getElem 130 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_htab_first_diff) rfl
    change originalRuntimeCode.lookup (ofString "htab_first_diff") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; decide
  · have hl := lookup_of_guestAst_getElem 137 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_htab_grow) rfl
    change originalRuntimeCode.lookup (ofString "htab_grow") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; decide
  · have hl := lookup_of_guestAst_getElem 134 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_htab_new_node) rfl
    change originalRuntimeCode.lookup (ofString "htab_new_node") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; decide
  · have hl := lookup_of_guestAst_getElem 136 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_htab_new_internal) rfl
    change originalRuntimeCode.lookup (ofString "htab_new_internal") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; decide
  · have hl := lookup_of_guestAst_getElem 135 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_htab_new_leaf) rfl
    change originalRuntimeCode.lookup (ofString "htab_new_leaf") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; decide
  · have hl := lookup_of_guestAst_getElem 138 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_htab_set) rfl
    change originalRuntimeCode.lookup (ofString "htab_set") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; decide
  · have hl := lookup_of_guestAst_getElem 139 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_htab_del) rfl
    change originalRuntimeCode.lookup (ofString "htab_del") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; decide
  · have hl := lookup_of_guestAst_getElem 356 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_jset) rfl
    change originalRuntimeCode.lookup (ofString "jset") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; decide
  · have hl := lookup_of_guestAst_getElem 357 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_jdel) rfl
    change originalRuntimeCode.lookup (ofString "jdel") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; decide

/-! ## 4. Non-Value `HtabExit` World-Step Lifting (9-conjunct `ArenaOK`) -/

theorem callee_param_three {F : Type} (state : PanSemStateFiniteExact 64 F) (fname p1 p2 p3 : MlS)
    (s1 s2 s3 : ShapeHOL) (body : ProgHOL 64) (ret : ShapeHOL)
    (hl : state.code.lookup fname = some ([(p1, s1), (p2, s2), (p3, s3)], body, ret))
    (e1 e2 e3 : ExpHOL 64)
    (values : List (ValueHOL 64)) (body' : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL)
    (hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [e1, e2, e3] = some values)
    (hlook : lookupCodeHOLFinite state.code.lookup fname values = some (body', callee, ret')) :
    ∃ v1 v2 v3,
      evalAt state e1 = some v1 ∧ evalAt state e2 = some v2 ∧ evalAt state e3 = some v3 ∧
      callee.lookup p1 = some v1 ∧ callee.lookup p2 = some v2 ∧ callee.lookup p3 = some v3 := by
  rw [evalListHOLFinite_eq_toExact] at hargs
  simp only [evalListHOLExact] at hargs
  rcases he1 : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) e1 with _ | v1
  · simp [he1] at hargs
  · rcases he2 : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) e2 with _ | v2
    · simp [he1, he2] at hargs
    · rcases he3 : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) e3 with _ | v3
      · simp [he1, he2, he3] at hargs
      · simp only [he1, he2, he3, Option.some.injEq] at hargs
        subst hargs
        unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hlook
        split at hlook
        · cases hlook
        · rename_i exactBody exactLocals exactShape raw
          have heq := Option.some.inj hlook
          rcases Prod.mk.inj heq with ⟨rfl, hrest⟩
          rcases Prod.mk.inj hrest with ⟨rfl, _⟩
          unfold lookupCodeHOLExact at raw
          rw [hl] at raw
          dsimp only at raw
          split at raw
          · rename_i hcond
            have rawEq := Option.some.inj raw
            rcases Prod.mk.inj rawEq with ⟨-, hrest2⟩
            rcases Prod.mk.inj hrest2 with ⟨hloc, -⟩
            subst hloc
            obtain ⟨hnd, -, -⟩ := hcond
            simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
              not_or, List.not_mem_nil, or_false] at hnd
            refine ⟨v1, v2, v3, he1, he2, he3, ?_, ?_, ?_⟩
            · simp [List.zip, List.foldl, hnd.1.1, hnd.1.2]
            · simp [List.zip, List.foldl, hnd.2.1]
            · simp [List.zip, List.foldl]
          · cases raw

theorem evalAt_loadG_nz {F : Type} (s : PanSemStateFiniteExact 64 F) (hG : GuestInv s)
    (g : String) (k : BitVec 64) (hk : k.toNat < sourceBase)
    (v : ValueHOL 64)
    (hev : evalAt s (.load .one (.op .add [.var .global (ofString g), .const k])) = some v) :
    ∃ a : BitVec 64, v = .val (.word a) ∧ a.toNat = memW s (globN s g + k.toNat) ∧
      globN s g ≠ 0 := by
  obtain ⟨a, rfl, ha⟩ := evalAt_loadG s g k v hev
  refine ⟨a, rfl, ha, ?_⟩
  intro hg0
  simp [evalAt, evalHOLExact, evalListHOLExact] at hev
  rcases hg : s.globals.lookup (ofString g) with _ | gv
  · simp [hg] at hev
  · rcases gv with ⟨⟨gw⟩⟩ | _ | _
    · have hgw0 : gw = 0 := by
        apply BitVec.eq_of_toNat_eq
        simpa [globN, hg] using hg0
      subst hgw0
      simp [hg, valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact, hG.memaddrs] at hev
      have hdom := (ordinaryDomain_iff k).1 hev.1
      omega
    · simp [hg, valueIsWord] at hev
    · simp [hg, valueIsWord] at hev

theorem disj_fresh_of_zero_or_allocated {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hAs : ArenaOK s) (hAp : ArenaOK post) (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    {j : Ivl} (hj : j.2 = 0 ∨ Allocated s j) :
    Disj j (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") := by
  have hsep : heapLimit ≤ scratchStart := by decide
  obtain ⟨_, hs_hp, hs_fm, hs_sc, _⟩ := hAs
  obtain ⟨_, hp_hp, _, _, _⟩ := hAp
  rcases hj with hz | ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
  · exact Or.inl hz
  · exact Or.inr (Or.inr (Or.inl (by dsimp; omega)))
  · exact Or.inr (Or.inr (Or.inr (by dsimp; omega)))

theorem htabFootprint_len_pos {F : Type} {s : PanSemStateFiniteExact 64 F} {t : Nat}
    (hwf : HtabWF s t) {i : Ivl} (hi : i ∈ htabFootprint s t) : i.2 ≠ 0 := by
  have hk1 : 1 ≤ hdr s t 0 := hwf.2.2.1
  have hst : hdr s t 1 = (hdr s t 0 + 7) / 8 * 8 := hwf.2.2.2.2.1
  have hnc : 2 ≤ hdr s t 10 := hwf.2.2.2.2.2.1
  simp only [htabFootprint, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · dsimp only; omega
  · dsimp only; rw [hst]
    have h1 : 8 ≤ (hdr s t 0 + 7) / 8 * 8 := by omega
    have h2 : 3 ≤ hdr s t 10 + 1 := by omega
    exact ne_of_gt (Nat.mul_pos (by omega) (by omega))
  · dsimp only; omega
  · dsimp only; omega

theorem mem_worldRoleSlots_recRole {F : Type} (s : PanSemStateFiniteExact 64 F)
    (g : String) (k : Nat) (r : String)
    (_hgnz : globN s g ≠ 0) (htnz : memW s (globN s g + k) ≠ 0)
    (hmem : (memW s (globN s g + k), r) ∈
      recRoles s "ws" [(16, "ws+16"), (32, "ws+32")] ++
      recRoles s "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"), (40, "bs+40"),
        (48, "bs+48"), (72, "bs+72")] ++
      recRoles s "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"), (40, "ts+40"),
        (48, "ts+48"), (56, "ts+56"), (64, "ts+64")]) :
    (memW s (globN s g + k), r) ∈ worldRoleSlots s := by
  unfold worldRoleSlots
  refine List.mem_filter.2 ⟨?_, by simp [htnz]⟩
  apply List.mem_append.2; left; apply List.mem_append.2; left
  apply List.mem_append.2; left; apply List.mem_append.2; left
  exact hmem

theorem slot_ne_of_diff_nonshared_role {F : Type} {s : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hroles : RolesOK s S (worldRoleSlots s) (journalRoleSlots s))
    {t1 t2 : Nat} {r1 r2 : String}
    (h1 : (t1, r1) ∈ worldRoleSlots s) (h2 : (t2, r2) ∈ worldRoleSlots s)
    (hne_r : r1 ≠ r2) :
    t1 ≠ t2 := by
  intro heq
  subst heq
  obtain ⟨i1, hi1, heq1⟩ := List.mem_iff_getElem.1 h1
  obtain ⟨i2, hi2, heq2⟩ := List.mem_iff_getElem.1 h2
  rcases Nat.lt_trichotomy i1 i2 with hlt | rfl | hgt
  · have hp := List.pairwise_iff_getElem.1 hroles.2.1 i1 i2 hi1 hi2 hlt
    rw [heq1, heq2] at hp
    exact hne_r (hp rfl).1
  · rw [heq1] at heq2
    exact hne_r (Prod.mk.inj heq2).2
  · have hp := List.pairwise_iff_getElem.1 hroles.2.1 i2 i1 hi2 hi1 hgt
    rw [heq1, heq2] at hp
    exact hne_r (hp rfl).1.symm

theorem balObjects_eq_of_unhit_except {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) {S : List Nat} (hT : TablesTyped s S) (hF : FixedTyped s)
    (hbal_eq : globN post "bal_accounts" = globN s "bal_accounts")
    {t0 : Nat}
    (hu_other : ∀ u ∈ S, u ≠ t0 → ∀ i ∈ htabFootprint s u, IvlUnhit s post i)
    (ht0_not_bal : globN s "bal_accounts" ≠ t0 ∧ ∀ ad ∈ balRecords s, memW s ad ≠ t0)
    (hu_bal : ∀ i ∈ balObjects s, i.2 ≠ 0 → IvlUnhit s post i)
    (hm0 : memW post 0 = memW s 0 ∧ memW post 8 = memW s 8 ∧ memW post 16 = memW s 16) :
    balObjects post = balObjects s ∧
    (∀ ad ∈ balRecords post, memW post ad = memW s ad ∧ memW post (ad + 8) = memW s (ad + 8) ∧
      htabValues post (memW post ad) = htabValues s (memW s ad) ∧
      (∀ k ∈ ([16, 24, 32] : List Nat), LstOK post (memW post (ad + k))) ∧
      (∀ l ∈ htabValues post (memW post ad), LstOK post l)) := by
  have hrecs : balRecords post = balRecords s :=
    balRecords_eq_of_unhit hT hbal_eq (fun hnz => by
      rcases hT.2.2.2.2.2.2.1 "bal_accounts" (by simp [globalTableRoots]) with h0 | hm
      · exact absurd h0 hnz
      · exact hu_other _ hm ht0_not_bal.1)
  have hmem_fix_of_bal : ∀ i ∈ balObjects s, i ∈ fixedObjects s := fun i hi => by
    unfold fixedObjects; exact List.mem_append.2 (Or.inr hi)
  have had_props : ∀ ad ∈ balRecords s,
      (∀ off ∈ ([0, 8, 16, 24, 32] : List Nat), memW post (ad + off) = memW s (ad + off)) ∧
      htabValues post (memW s ad) = htabValues s (memW s ad) ∧
      (∀ k ∈ ([16, 24, 32] : List Nat), memW s (ad + k) ≠ 0 →
        memW post (memW s (ad + k)) = memW s (memW s (ad + k)) ∧
        memW post (memW s (ad + k) + 8) = memW s (memW s (ad + k) + 8) ∧
        memW post (memW s (ad + k) + 16) = memW s (memW s (ad + k) + 16)) ∧
      (∀ l ∈ htabValues s (memW s ad), l ≠ 0 →
        memW post l = memW s l ∧ memW post (l + 8) = memW s (l + 8) ∧ memW post (l + 16) = memW s (l + 16)) := by
    intro ad had
    have had_bal : (ad, 40) ∈ balObjects s := by
      unfold balObjects; exact List.mem_flatMap.2 ⟨ad, had, by simp⟩
    rcases hF.1 _ (hmem_fix_of_bal _ had_bal) with h0 | ⟨hal_ad, hw_ad⟩
    · simp at h0
    have hhi_ad := (ivl_allocated_bound hA hal_ad).2
    have had8 : ad % 8 = 0 := hw_ad.1
    have hoff_eq : ∀ off ∈ ([0, 8, 16, 24, 32] : List Nat), memW post (ad + off) = memW s (ad + off) := by
      intro off hoff
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
      rcases hoff with rfl | rfl | rfl | rfl | rfl <;>
        exact memW_eq_of_ivlUnhit (hu_bal _ had_bal (by simp)) (by omega) hhi_ad ⟨by omega, by omega⟩
    have had_T := hT.2.2.2.2.2.2.2.2.2.1 ad had
    have hvals_ad : htabValues post (memW s ad) = htabValues s (memW s ad) :=
      htabValues_eq_of_unhit (hT.2.1 _ had_T.1).1 (hu_other _ had_T.1 (ht0_not_bal.2 ad had))
    have hlst_eq : ∀ l, (l, 24) ∈ balObjects s →
        memW post l = memW s l ∧ memW post (l + 8) = memW s (l + 8) ∧ memW post (l + 16) = memW s (l + 16) := by
      intro l hl_bal
      rcases hF.1 _ (hmem_fix_of_bal _ hl_bal) with h0 | ⟨hal_l, hw_l⟩
      · simp at h0
      have hhi_l := (ivl_allocated_bound hA hal_l).2
      have hl8 : l % 8 = 0 := hw_l.1
      have hul := hu_bal _ hl_bal (by simp)
      refine ⟨?_, ?_, ?_⟩
      · simpa using memW_eq_of_ivlUnhit hul (by omega) hhi_l ⟨by omega, by omega⟩
      · exact memW_eq_of_ivlUnhit hul (by omega) hhi_l ⟨by omega, by omega⟩
      · exact memW_eq_of_ivlUnhit hul (by omega) hhi_l ⟨by omega, by omega⟩
    refine ⟨hoff_eq, hvals_ad, ?_, ?_⟩
    · intro k hk hnz
      apply hlst_eq
      unfold balObjects
      refine List.mem_flatMap.2 ⟨ad, had, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl <;> simp [lstObjects, hnz]
    · intro l hl hnz
      apply hlst_eq
      unfold balObjects
      refine List.mem_flatMap.2 ⟨ad, had, ?_⟩
      apply List.mem_cons_of_mem; apply List.mem_append.2; right
      exact List.mem_flatMap.2 ⟨l, hl, by simp [lstObjects, hnz]⟩
  constructor
  · unfold balObjects
    rw [hrecs]
    apply List.flatMap_congr
    intro ad had
    obtain ⟨hoff_eq, hvals_ad, hklst, hllst⟩ := had_props ad had
    have h0 := hoff_eq 0 (by simp); simp only [Nat.add_zero] at h0
    have h16 := hoff_eq 16 (by simp)
    have h24 := hoff_eq 24 (by simp)
    have h32 := hoff_eq 32 (by simp)
    have hlst_congr : ∀ k esz, k ∈ ([16, 24, 32] : List Nat) →
        lstObjects post (memW s (ad + k)) esz = lstObjects s (memW s (ad + k)) esz := by
      intro k esz hk
      by_cases hkz : memW s (ad + k) = 0
      · simp [lstObjects, hkz]
      · obtain ⟨hc0, _, hc16⟩ := hklst k hk hkz
        simp [lstObjects, hkz, hc0, hc16]
    have htail : (htabValues post (memW post ad)).flatMap (fun l => lstObjects post l 40) =
        (htabValues s (memW s ad)).flatMap (fun l => lstObjects s l 40) := by
      rw [h0, hvals_ad]
      apply List.flatMap_congr
      intro l hl
      by_cases hlz : l = 0
      · simp [lstObjects, hlz]
      · obtain ⟨hl0, _, hl16⟩ := hllst l hl hlz
        simp [lstObjects, hlz, hl0, hl16]
    rw [htail, h16, h24, h32, hlst_congr 16 40 (by simp), hlst_congr 24 16 (by simp), hlst_congr 32 24 (by simp)]
  · intro ad had
    rw [hrecs] at had
    obtain ⟨hoff_eq, hvals_ad, hklst, hllst⟩ := had_props ad had
    have had_T := hT.2.2.2.2.2.2.2.2.2.1 ad had
    have h0 := hoff_eq 0 (by simp); simp only [Nat.add_zero] at h0
    have h8 := hoff_eq 8 (by simp)
    refine ⟨h0, h8, by rw [h0, hvals_ad], ?_, ?_⟩
    · intro k hk
      have hk_in : k ∈ ([0, 8, 16, 24, 32] : List Nat) := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk ⊢
        rcases hk with rfl | rfl | rfl <;> simp
      rw [hoff_eq k hk_in]
      by_cases hkz : memW s (ad + k) = 0
      · unfold LstOK; rw [hkz]; simp [hm0.2.1, hm0.2.2]; simpa [LstOK, hkz] using had_T.2.2.1 k hk
      · obtain ⟨_, hk8, hk16⟩ := hklst k hk hkz
        unfold LstOK; rw [hk8, hk16]; exact had_T.2.2.1 k hk
    · intro l hl
      rw [h0, hvals_ad] at hl
      by_cases hlz : l = 0
      · unfold LstOK; rw [hlz]; simp [hm0.2.1, hm0.2.2]; simpa [LstOK, hlz] using had_T.2.2.2 l hl
      · obtain ⟨_, hl8, hl16⟩ := hllst l hl hlz
        unfold LstOK; rw [hl8, hl16]; exact had_T.2.2.2 l hl

theorem worldRoleSlots_eq_of_unhit_except {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) {S : List Nat} (hT : TablesTyped s S) (hF : FixedTyped s)
    (hcore : ∀ g ∈ coreWorldGlobals, globN post g = globN s g)
    {t0 : Nat}
    (hu_other : ∀ u ∈ S, u ≠ t0 → ∀ i ∈ htabFootprint s u, IvlUnhit s post i)
    (ht0_not_nest : (globN s "bs" ≠ 0 → memW s (globN s "bs" + 32) ≠ t0) ∧
                    (globN s "ts" ≠ 0 → memW s (globN s "ts" + 32) ≠ t0) ∧
                    globN s "bal_accounts" ≠ t0 ∧ ∀ ad ∈ balRecords s, memW s ad ≠ t0)
    (hu_ws : globN s "ws" ≠ 0 → IvlUnhit s post (globN s "ws", 40))
    (hu_bs : globN s "bs" ≠ 0 → IvlUnhit s post (globN s "bs", 80))
    (hu_ts : globN s "ts" ≠ 0 → IvlUnhit s post (globN s "ts", 72))
    (hu_bal : ∀ i ∈ balObjects s, i.2 ≠ 0 → IvlUnhit s post i)
    (hm0 : memW post 0 = memW s 0 ∧ memW post 8 = memW s 8 ∧ memW post 16 = memW s 16) :
    worldRoleSlots post = worldRoleSlots s := by
  have hws_g : globN post "ws" = globN s "ws" := hcore "ws" (by decide)
  have hbs_g : globN post "bs" = globN s "bs" := hcore "bs" (by decide)
  have hts_g : globN post "ts" = globN s "ts" := hcore "ts" (by decide)
  have hba_g : globN post "bal_accounts" = globN s "bal_accounts" := hcore "bal_accounts" (by decide)
  have hbia_g : globN post "bal_idx_accts" = globN s "bal_idx_accts" := hcore "bal_idx_accts" (by decide)
  have hbis_g : globN post "bal_idx_stor" = globN s "bal_idx_stor" := hcore "bal_idx_stor" (by decide)
  have hrec_ws : recRoles post "ws" [(16, "ws+16"), (32, "ws+32")] =
      recRoles s "ws" [(16, "ws+16"), (32, "ws+32")] := by
    unfold recRoles
    by_cases h : globN s "ws" = 0
    · simp [hws_g, h]
    · simp only [hws_g, h, ↓reduceIte]
      apply List.map_congr_left
      intro ⟨k, r⟩ hkr
      have hk : k % 8 = 0 ∧ k + 8 ≤ 40 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hkr
        rcases hkr with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
      have hw := rec_word_eq_of_unhit hA hF "ws" 40 (by simp [typedRecords]) hws_g h (hu_ws h) hk.1 hk.2
      simp only [hws_g] at hw; simp [hw]
  have hrec_bs : recRoles post "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"),
      (40, "bs+40"), (48, "bs+48"), (72, "bs+72")] =
      recRoles s "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"),
      (40, "bs+40"), (48, "bs+48"), (72, "bs+72")] := by
    unfold recRoles
    by_cases h : globN s "bs" = 0
    · simp [hbs_g, h]
    · simp only [hbs_g, h, ↓reduceIte]
      apply List.map_congr_left
      intro ⟨k, r⟩ hkr
      have hk : k % 8 = 0 ∧ k + 8 ≤ 80 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hkr
        rcases hkr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
      have hw := rec_word_eq_of_unhit hA hF "bs" 80 (by simp [typedRecords]) hbs_g h (hu_bs h) hk.1 hk.2
      simp only [hbs_g] at hw; simp [hw]
  have hrec_ts : recRoles post "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"),
      (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] =
      recRoles s "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"),
      (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] := by
    unfold recRoles
    by_cases h : globN s "ts" = 0
    · simp [hts_g, h]
    · simp only [hts_g, h, ↓reduceIte]
      apply List.map_congr_left
      intro ⟨k, r⟩ hkr
      have hk : k % 8 = 0 ∧ k + 8 ≤ 72 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hkr
        rcases hkr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
      have hw := rec_word_eq_of_unhit hA hF "ts" 72 (by simp [typedRecords]) hts_g h (hu_ts h) hk.1 hk.2
      simp only [hts_g] at hw; simp [hw]
  have hnest_bs : nestRoles post "bs" "bs.inner" = nestRoles s "bs" "bs.inner" := by
    unfold nestRoles
    by_cases h : globN s "bs" = 0
    · simp [hbs_g, h]
    · have hw32 := rec_word_eq_of_unhit hA hF "bs" 80 (by simp [typedRecords]) hbs_g h (hu_bs h) (k := 32) (by omega) (by omega)
      simp only [hbs_g] at hw32 ⊢
      simp only [h, ↓reduceIte, hw32]
      by_cases h32 : memW s (globN s "bs" + 32) = 0
      · simp [h32]
      · simp only [h32, ↓reduceIte]
        have hmS : memW s (globN s "bs" + 32) ∈ S := by
          rcases hT.2.2.2.2.1 32 (by simp [bsTableSlots]) h with h0 | hm
          · exact absurd h0 h32
          · exact hm
        rw [htabValues_eq_of_unhit (hT.2.1 _ hmS).1 (hu_other _ hmS (ht0_not_nest.1 h))]
  have hnest_ts : nestRoles post "ts" "ts.inner" = nestRoles s "ts" "ts.inner" := by
    unfold nestRoles
    by_cases h : globN s "ts" = 0
    · simp [hts_g, h]
    · have hw32 := rec_word_eq_of_unhit hA hF "ts" 72 (by simp [typedRecords]) hts_g h (hu_ts h) (k := 32) (by omega) (by omega)
      simp only [hts_g] at hw32 ⊢
      simp only [h, ↓reduceIte, hw32]
      by_cases h32 : memW s (globN s "ts" + 32) = 0
      · simp [h32]
      · simp only [h32, ↓reduceIte]
        have hmS : memW s (globN s "ts" + 32) ∈ S := by
          rcases hT.2.2.2.2.2.1 32 (by simp [tsTableSlots]) h with h0 | hm
          · exact absurd h0 h32
          · exact hm
        rw [htabValues_eq_of_unhit (hT.2.1 _ hmS).1 (hu_other _ hmS (ht0_not_nest.2.1 h))]
  have hrecs_bal := balRecords_eq_of_unhit hT hba_g (fun hnz => by
    rcases hT.2.2.2.2.2.2.1 "bal_accounts" (by simp [globalTableRoots]) with h0 | hm
    · exact absurd h0 hnz
    · exact hu_other _ hm ht0_not_nest.2.2.1)
  have hbal_part := (balObjects_eq_of_unhit_except hA hT hF hba_g hu_other
    ⟨ht0_not_nest.2.2.1, ht0_not_nest.2.2.2⟩ hu_bal hm0).2
  unfold worldRoleSlots
  rw [hrec_ws, hrec_bs, hrec_ts, hba_g, hbia_g, hbis_g, hnest_bs, hnest_ts, hrecs_bal]
  congr 1; congr 1
  apply List.flatMap_congr
  intro ad had
  rw [← hrecs_bal] at had
  obtain ⟨h0, h8, _⟩ := hbal_part ad had
  rw [h0, h8]

theorem worldStepSc_of_htabExit_nonValue {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)} {gw : List String}
    (hW0 : WorldOK s) (hbe : post.be = s.be)
    (hg_kept : GlobalsKept gw s post)
    (hg_nonHeap : ∀ k : MlS, k ∉ (["heap_ptr"] : List String).map ofString →
      s.globals.lookup k = post.globals.lookup k)
    {t0 : Nat}
    (ht0_mem : ∀ S, TablesTyped s S → t0 ∈ S ∧
      (globN s "bs" ≠ 0 → memW s (globN s "bs" + 32) ≠ t0) ∧
      (globN s "ts" ≠ 0 → memW s (globN s "ts" + 32) ≠ t0) ∧
      globN s "bal_accounts" ≠ t0 ∧
      (∀ ad ∈ balRecords s, memW s ad ≠ t0) ∧
      (globN s "ws" ≠ 0 → memW s (globN s "ws" + 32) ≠ t0))
    (hAp : ArenaReady post) (hwf_t0 : HtabWF post t0)
    (hhdr0_t0 : hdr post t0 0 = hdr s t0 0)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hfp_t0 : ∀ i ∈ htabFootprint post t0, Allocated post i ∧
      ((∃ j ∈ htabFootprint s t0, Inside i j.1 (j.1 + j.2)) ∨
        Inside i (globN s "heap_ptr") (globN s "heap_ptr" + (globN post "heap_ptr" - globN s "heap_ptr"))))
    (hfr : FrameOutside s post (htabFootprint s t0) (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr")) :
    WorldStepSc (bufRegions []) gw stdKeep NoExtra s r post := by
  have hAs := hW0.1
  have hsp_eq : globN post "scratch_ptr" = globN s "scratch_ptr" :=
    globN_eq_of_lookup (hg_nonHeap (ofString "scratch_ptr") (by decide))
  have hag : AllocatorGrows s post := ⟨hhp, by rw [hsp_eq]⟩
  have hcore : ∀ g ∈ coreWorldGlobals, globN post g = globN s g := fun g hg => by
    have hne : ofString g ∉ (["heap_ptr"] : List String).map ofString := by revert g hg; decide
    exact globN_eq_of_lookup (hg_nonHeap (ofString g) hne)
  have hbuf_same : FreshBufsOK s post := by
    refine ⟨fun gn hgn => Or.inl ?_, List.pairwise_iff_getElem.2 fun i j _ _ _ ha _ => absurd ?_ ha.1⟩
    · have hne : ofString gn.1 ∉ (["heap_ptr"] : List String).map ofString := by revert gn hgn; decide
      exact globN_eq_of_lookup (hg_nonHeap (ofString gn.1) hne)
    · have hgm := List.getElem_mem ‹i < globalBuffers.length›
      have hne : ofString globalBuffers[i].1 ∉ (["heap_ptr"] : List String).map ofString := by
        revert hgm; generalize globalBuffers[i] = gp; intro hgm; revert gp hgm; decide
      exact globN_eq_of_lookup (hg_nonHeap (ofString globalBuffers[i].1) hne)
  obtain ⟨S0, hWT0_ex⟩ := hW0.2
  obtain ⟨Nd0, hWT0⟩ := (worldTyped_iff_with s S0).1 hWT0_ex
  have ht0_S0 : t0 ∈ S0 := (ht0_mem S0 hWT0.1).1
  have hf_al : (globN s "heap_ptr") % 8 = 0 ∧ (globN post "heap_ptr" - globN s "heap_ptr") % 8 = 0 := by
    have h1 := hAs.2.2.2.2.2.2.1
    have h2 := hAp.2.2.2.2.2.2.1
    omega
  have ht0_al0 : ∀ j ∈ htabFootprint s t0, j.1 % 8 = 0 ∧ j.2 % 8 = 0 := fun j hj => by
    have hw := ((hWT0.1.2.1 t0 ht0_S0).1.1 j hj).2
    exact ⟨hw.1, hw.2.1⟩
  have hrk : RecordsKept (bufRegions []) stdKeep s post := by
    intro rec hrec hgnz k hk _
    have hrec_sz : ∃ sz, (rec.1, sz) ∈ typedRecords ∧ sz ≠ 0 ∧ k % 8 = 0 ∧ k + 8 ≤ sz := by
      simp only [stdKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
      rcases hrec with rfl | rfl | rfl | rfl
      · refine ⟨40, by simp [typedRecords], by decide, ?_⟩; simp at hk; omega
      · refine ⟨80, by simp [typedRecords], by decide, ?_⟩; simp at hk; omega
      · refine ⟨72, by simp [typedRecords], by decide, ?_⟩; simp at hk; omega
      · refine ⟨88, by simp [typedRecords], by decide, ?_⟩; simp at hk; omega
    obtain ⟨sz, htr, hsz_nz, hk8, hksz⟩ := hrec_sz
    have hmf := typedRecord_mem_fixedObjects s htr
    simp only [hgnz, ↓reduceIte] at hmf
    rcases hWT0.2.2.1.1 _ hmf with h0 | ⟨hal, hwords⟩
    · omega
    · have hhi := (ivl_allocated_bound hAs.2 hal).2
      have hg8 : (globN s rec.1) % 8 = 0 := hwords.1
      have hu_rec : IvlUnhit s post (globN s rec.1, sz) :=
        ivlUnhit_of_frameOutside_aligned hsz_nz hfr ht0_al0 hf_al
          (fun j hj => (((hWT0.1.2.1 t0 ht0_S0).2 j hj).2 _ hmf).flip)
          (disj_fresh_of_zero_or_allocated hAs.2 hAp.2 hhp (Or.inr hal))
      exact memW_eq_of_ivlUnhit hu_rec (by omega) hhi ⟨by omega, by omega⟩
  refine ⟨⟨hAp, hhp, hg_kept, hrk, fun S Nd hWT _ => ?_⟩, by rw [hsp_eq]⟩
  obtain ⟨hT, hJ, hF, hTr⟩ := hWT
  obtain ⟨ht0_S, hno_bs32, hno_ts32, hno_ba, hno_ad, hno_ws32⟩ := ht0_mem S hT
  have ht0_al : ∀ j ∈ htabFootprint s t0, j.1 % 8 = 0 ∧ j.2 % 8 = 0 := fun j hj => by
    have hw := ((hT.2.1 t0 ht0_S).1.1 j hj).2
    exact ⟨hw.1, hw.2.1⟩
  have hunhit_disj : ∀ i : Ivl, i.2 ≠ 0 → (∀ j ∈ htabFootprint s t0, Disj i j) →
      Allocated s i → IvlUnhit s post i := fun i hipos hdi hal =>
    ivlUnhit_of_frameOutside_aligned hipos hfr ht0_al hf_al hdi
      (disj_fresh_of_zero_or_allocated hAs.2 hAp.2 hhp (Or.inr hal))
  have hu_other : ∀ u ∈ S, u ≠ t0 → ∀ i ∈ htabFootprint s u, IvlUnhit s post i := fun u hu hne i hi =>
    hunhit_disj i (htabFootprint_len_pos (hT.2.1 u hu).1 hi)
      (fun j hj => hT.2.2.1 u hu t0 ht0_S hne i hi j hj)
      (((hT.2.1 u hu).2 i hi).1)
  have hu_fix : ∀ i ∈ fixedObjects s, i.2 ≠ 0 → IvlUnhit s post i := fun i hi hipos =>
    hunhit_disj i hipos (fun j hj => (((hT.2.1 t0 ht0_S).2 j hj).2 i hi).flip)
      (by
        rcases hF.1 i hi with h0 | ⟨hal, _⟩
        · exact absurd h0 hipos
        · exact hal)
  have hu_nd_rec : ∀ n ∈ Nd, IvlUnhit s post (nodeIvl s n) := fun n hn => by
    have hmem : nodeIvl s n ∈ nodeExtents s Nd := by
      unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, by simp⟩
    have hpos : (nodeIvl s n).2 ≠ 0 := by
      dsimp [nodeIvl]; unfold nodeSize; split_ifs <;> decide
    exact hunhit_disj _ hpos (fun j hj => (hTr.2.1 _ hmem).1 t0 ht0_S j hj)
      ((hTr.1.1 n hn).2.1)
  have hu_nd_byte : ∀ n ∈ Nd, (memW s n = 1 ∨ memW s n = 2) → memW s (n + 40) ≠ 0 →
      ∀ k, k < memW s (n + 40) → memB post (memW s (n + 32) + k) = memB s (memW s (n + 32) + k) := by
    intro n hn h12 hlen0 k hk
    have h264 : heapLimit ≤ 2 ^ 64 := by decide
    rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 h12 with h0 | ⟨_, hal_p, hin_p, _⟩
    · exact absurd h0 hlen0
    · have hp_ne : (memW s (n + 32), memW s (n + 40)) ∈ nodeExtents s Nd := by
        unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, by simp [nodePath, h12, hlen0]⟩
      have ha_lt : memW s (n + 32) + k < 2 ^ 64 := by have := hin_p.2; omega
      let c := panByteAlignHOL (BitVec.ofNat 64 (memW s (n + 32) + k))
      have hc_nat : c.toNat = (memW s (n + 32) + k) / 8 * 8 := by
        rw [panByteAlign_toNat64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]
      have hmem := hfr c
        (fun j hj hcj => by
          obtain ⟨h1, h2⟩ := hcj
          rw [hc_nat] at h1 h2
          have hj_al := ((hT.2.1 t0 ht0_S).1.1 j hj).2
          have hj1 := hj_al.1; have hj2 := hj_al.2.1
          have hdj := (hTr.2.1 _ hp_ne).1 t0 ht0_S j hj
          rcases hdj with d | d | d | d <;> omega)
        (fun hcf => by
          obtain ⟨h1, h2⟩ := hcf
          dsimp at h1 h2
          rw [hc_nat] at h1 h2
          have hp_hp8 : (globN post "heap_ptr") % 8 = 0 := hAp.2.2.2.2.2.2.1
          have hdj := disj_fresh_of_zero_or_allocated hAs.2 hAp.2 hhp (Or.inr hal_p)
          try dsimp at hdj
          rcases hdj with d | d | d | d <;> omega)
      unfold memB
      change (match post.memory c with | .word v => (panGetByteHOL (BitVec.ofNat 64 (memW s (n + 32) + k)) v post.be).toNat) =
             (match s.memory c with | .word v => (panGetByteHOL (BitVec.ofNat 64 (memW s (n + 32) + k)) v s.be).toNat)
      rw [hmem, hbe]
  have hm0 : memW post 0 = memW s 0 ∧ memW post 8 = memW s 8 ∧ memW post 16 = memW s 16 := by
    have hlow : ∀ a : Nat, a + 8 ≤ sourceBase → memW post a = memW s a := fun a ha => by
      have hsb_lt : sourceBase < 2 ^ 64 := by decide
      have ha_lt : a < 2 ^ 64 := lt_of_le_of_lt (by omega) hsb_lt
      have hm := hfr (BitVec.ofNat 64 a)
        (fun j hj hcj => by
          obtain ⟨h1, _⟩ := hcj
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt] at h1
          have hlo := ((hT.2.1 t0 ht0_S).1.1 j hj).1.1
          omega)
        (fun hcf => by
          obtain ⟨h1, _⟩ := hcf
          dsimp at h1
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt] at h1
          have hlo := hAs.2.1
          omega)
      unfold memW; rw [hm]
    exact ⟨hlow 0 (by decide), hlow 8 (by decide), hlow 16 (by decide)⟩
  have hu_ws : globN s "ws" ≠ 0 → IvlUnhit s post (globN s "ws", 40) := fun hnz => by
    have hm := typedRecord_mem_fixedObjects s (r := ("ws", 40)) (by simp [typedRecords])
    simp only [hnz, ↓reduceIte] at hm; exact hu_fix _ hm (by dsimp only; omega)
  have hu_bs : globN s "bs" ≠ 0 → IvlUnhit s post (globN s "bs", 80) := fun hnz => by
    have hm := typedRecord_mem_fixedObjects s (r := ("bs", 80)) (by simp [typedRecords])
    simp only [hnz, ↓reduceIte] at hm; exact hu_fix _ hm (by dsimp only; omega)
  have hu_ts : globN s "ts" ≠ 0 → IvlUnhit s post (globN s "ts", 72) := fun hnz => by
    have hm := typedRecord_mem_fixedObjects s (r := ("ts", 72)) (by simp [typedRecords])
    simp only [hnz, ↓reduceIte] at hm; exact hu_fix _ hm (by dsimp only; omega)
  have hu_bo : globN s "bo" ≠ 0 → IvlUnhit s post (globN s "bo", 88) := fun hnz => by
    have hm := typedRecord_mem_fixedObjects s (r := ("bo", 88)) (by simp [typedRecords])
    simp only [hnz, ↓reduceIte] at hm; exact hu_fix _ hm (by dsimp only; omega)
  have hu_jr : globN s "journal_cap" ≠ 0 → IvlUnhit s post (globN s "journal", 32 * globN s "journal_cap") := fun hnz => by
    apply hu_fix _ _ (by dsimp only; omega)
    unfold fixedObjects
    apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right
    simp [hnz]
  have hu_bo_lst : ∀ i ∈ blockOutObjects s, i.2 = 24 → IvlUnhit s post i := fun i hi h24 =>
    hu_fix i (by unfold fixedObjects; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hi)))) (by omega)
  have hu_bal : ∀ i ∈ balObjects s, i.2 ≠ 0 → IvlUnhit s post i := fun i hi hipos =>
    hu_fix i (by unfold fixedObjects; exact List.mem_append.2 (Or.inr hi)) hipos
  have hbo_eq := blockOutObjects_eq_of_bo_unhit hAs.2 hF (hcore "bo" (by decide))
    hT.2.2.2.2.2.2.2.2.2.2.1 hu_bo hu_bo_lst
  have hbal_eq := balObjects_eq_of_unhit_except hAs.2 hT hF
    (hcore "bal_accounts" (by decide)) hu_other ⟨hno_ba, hno_ad⟩ hu_bal hm0
  obtain ⟨hF_post, _⟩ := fixedTyped_of_freshBufsOK hAs hAp hag hF
    (hcore "journal" (by decide)) (hcore "journal_cap" (by decide)) hbo_eq.1 hbal_eq.1 hbuf_same
  have hfix_eq : fixedObjects post = fixedObjects s := by
    unfold fixedObjects
    rw [hbo_eq.1, hbal_eq.1, hcore "journal" (by decide), hcore "journal_cap" (by decide)]
    congr 3
    apply List.map_congr_left
    intro gn hgn
    have hne : ofString gn.1 ∉ (["heap_ptr"] : List String).map ofString := by revert gn hgn; decide
    have hg_eq : globN post gn.1 = globN s gn.1 := globN_eq_of_lookup (hg_nonHeap (ofString gn.1) hne)
    simp [hg_eq]
  obtain ⟨hjr_eq, hJ_post⟩ := journalRoleSlots_eq_of_unhit
    hAs.1 hAp.1 hAs.2 hag (fun _ hx => hx) hJ hF hcore hu_ts hu_jr
  have hwrs_eq := worldRoleSlots_eq_of_unhit_except hAs.2 hT hF hcore hu_other
    ⟨hno_bs32, hno_ts32, hno_ba, hno_ad⟩ hu_ws hu_bs hu_ts hu_bal hm0
  obtain ⟨hNH_post, hne_eq⟩ := nodeHeap_congr_bytes
    hAs.1 hAp.1 hag hTr.1 hu_nd_rec hu_nd_byte
  have h264 : heapEnd ≤ 2 ^ 64 := by decide
  have hother_fp : ∀ u ∈ S, u ≠ t0 →
      (∀ k, k < 11 → hdr post u k = hdr s u k) ∧ htabFootprint post u = htabFootprint s u := by
    intro u hu hne
    have hfp := (hT.2.1 u hu).1.1
    have ht_fp : (u, 88) ∈ htabFootprint s u := by simp [htabFootprint]
    exact htabFootprint_eq_of_hdr_unhit ((hfp _ ht_fp).2.1)
      (by have := (hfp _ ht_fp).1.2; dsimp at this; omega) (hu_other u hu hne _ ht_fp)
  have ht0_disj_other : ∀ i ∈ htabFootprint post t0,
      (∀ u ∈ S, u ≠ t0 → ∀ j ∈ htabFootprint s u, Disj i j) ∧
      (∀ j ∈ fixedObjects s, Disj i j) ∧
      (∀ o ∈ nodeExtents s Nd, Disj i o) := by
    intro i hi
    rcases (hfp_t0 i hi).2 with ⟨k, hk, hin⟩ | hfresh
    · refine ⟨fun u hu hne j hj => disj_of_inside_left hin (hT.2.2.1 t0 ht0_S u hu hne.symm k hk j hj),
              fun j hj => disj_of_inside_left hin (((hT.2.1 t0 ht0_S).2 k hk).2 j hj),
              fun o ho => disj_of_inside_left hin ((hTr.2.1 o ho).1 t0 ht0_S k hk).flip⟩
    · refine ⟨fun u hu _ j hj => (disj_of_inside_right hfresh
                (disj_fresh_of_zero_or_allocated hAs.2 hAp.2 hhp (Or.inr ((hT.2.1 u hu).2 j hj).1))).flip,
              fun j hj => (disj_of_inside_right hfresh
                (disj_fresh_of_zero_or_allocated hAs.2 hAp.2 hhp
                  (by rcases hF.1 j hj with h0 | ⟨hal, _⟩; exact Or.inl h0; exact Or.inr hal))).flip,
              fun o ho => (disj_of_inside_right hfresh
                (disj_fresh_of_zero_or_allocated hAs.2 hAp.2 hhp (by
                  unfold nodeExtents at ho
                  obtain ⟨n, hn, hno⟩ := List.mem_flatMap.1 ho
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hno
                  rcases hno with rfl | rfl
                  · exact Or.inr (hTr.1.1 n hn).2.1
                  · unfold nodePath; split_ifs with hc
                    · rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 hc.1 with h0 | ⟨_, hal, _⟩
                      · exact absurd h0 hc.2
                      · exact Or.inr hal
                    · exact Or.inl rfl))).flip⟩
  have hT_post : TablesTyped post S := by
    have hT0 := hT
    obtain ⟨hnd, htwf, htpw, hwsR, hbsR, htsR, hgR, hbsN, htsN, hbalT, _, hroles⟩ := hT
    have ews := hcore "ws" (by decide)
    have ebs := hcore "bs" (by decide)
    have ets := hcore "ts" (by decide)
    refine ⟨hnd, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hbo_eq.2, ?_⟩
    · intro u hu
      by_cases heq : u = t0
      · subst heq; rw [hfix_eq]
        exact ⟨hwf_t0, fun i hi => ⟨(hfp_t0 i hi).1, (ht0_disj_other i hi).2.1⟩⟩
      · rw [(hother_fp u hu heq).2, hfix_eq]
        exact ⟨htabWF_congr_unhit hAs.1 hAp.1 (htwf u hu).1 (hu_other u hu heq),
          fun i hi => ⟨hag.allocated ((htwf u hu).2 i hi).1, ((htwf u hu).2 i hi).2⟩⟩
    · intro u hu v hv hne i hi j hj
      by_cases hu0 : u = t0
      · subst hu0; rw [(hother_fp v hv hne.symm).2] at hj
        exact (ht0_disj_other i hi).1 v hv hne.symm j hj
      · by_cases hv0 : v = t0
        · subst hv0; rw [(hother_fp u hu hu0).2] at hi
          exact ((ht0_disj_other j hj).1 u hu hu0 i hi).flip
        · rw [(hother_fp u hu hu0).2] at hi; rw [(hother_fp v hv hv0).2] at hj
          exact htpw u hu v hv hne i hi j hj
    · intro k hk hnz
      rw [ews] at hnz
      have hk8 : k % 8 = 0 ∧ k + 8 ≤ 40 := by
        simp only [wsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl <;> omega
      rw [rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by simp [typedRecords]) ews hnz (hu_ws hnz) hk8.1 hk8.2]
      exact hwsR k hk hnz
    · intro k hk hnz
      rw [ebs] at hnz
      have hk8 : k % 8 = 0 ∧ k + 8 ≤ 80 := by
        simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by simp [typedRecords]) ebs hnz (hu_bs hnz) hk8.1 hk8.2]
      exact hbsR k hk hnz
    · intro k hk hnz
      rw [ets] at hnz
      have hk8 : k % 8 = 0 ∧ k + 8 ≤ 72 := by
        simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) ets hnz (hu_ts hnz) hk8.1 hk8.2]
      exact htsR k hk hnz
    · intro g hg_mem; rw [hcore g (by simp only [globalTableRoots, List.mem_cons, List.not_mem_nil, or_false] at hg_mem; rcases hg_mem with rfl | rfl | rfl <;> decide)]; exact hgR g hg_mem
    · intro hnz hmem
      rw [ebs] at hnz
      have ew := rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by simp [typedRecords]) ebs hnz (hu_bs hnz) (k := 32) (by omega) (by omega)
      rw [ew] at hmem ⊢
      exact htabValuesIn_congr_unhit (htwf _ hmem).1 (hu_other _ hmem (hno_bs32 hnz)) (fun _ hx => hx) (hbsN hnz hmem)
    · intro hnz hmem
      rw [ets] at hnz
      have ew := rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) ets hnz (hu_ts hnz) (k := 32) (by omega) (by omega)
      rw [ew] at hmem ⊢
      exact htabValuesIn_congr_unhit (htwf _ hmem).1 (hu_other _ hmem (hno_ts32 hnz)) (fun _ hx => hx) (htsN hnz hmem)
    · intro ad had
      have had_s : ad ∈ balRecords s := by
        rwa [balRecords_eq_of_unhit hT0 (hcore "bal_accounts" (by decide)) (fun hnz => by
          rcases hgR "bal_accounts" (by simp [globalTableRoots]) with h0 | hm
          · exact absurd h0 hnz
          · exact hu_other _ hm hno_ba)] at had
      obtain ⟨e0, e8, _, hkl, hll⟩ := hbal_eq.2 ad had
      exact ⟨e0 ▸ (hbalT ad had_s).1, e8 ▸ (hbalT ad had_s).2.1, hkl, hll⟩
    · unfold RolesOK at hroles ⊢
      rw [hwrs_eq, hjr_eq]
      refine ⟨fun a ha => ?_, hroles.2⟩
      obtain ⟨haS, hkl⟩ := hroles.1 a ha
      by_cases ha0 : a.1 = t0
      · rw [ha0] at hkl ⊢; exact ⟨ht0_S, hhdr0_t0.trans hkl⟩
      · exact ⟨haS, ((hother_fp a.1 haS ha0).1 0 (by omega)).trans hkl⟩
  have hTr_post : TriesTypedWith post S Nd := by
    have ews := hcore "ws" (by decide)
    refine ⟨hNH_post, ?_, ?_⟩
    · rw [hne_eq, hfix_eq]
      intro o ho
      refine ⟨fun u hu i hi => ?_, (hTr.2.1 o ho).2⟩
      by_cases hu0 : u = t0
      · subst hu0; exact ((ht0_disj_other i hi).2.2 o ho).flip
      · rw [(hother_fp u hu hu0).2] at hi; exact (hTr.2.1 o ho).1 u hu i hi
    · intro hws_nz
      rw [ews] at hws_nz
      have e24 := rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by simp [typedRecords]) ews hws_nz (hu_ws hws_nz) (k := 24) (by omega) (by omega)
      have e32 := rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by simp [typedRecords]) ews hws_nz (hu_ws hws_nz) (k := 32) (by omega) (by omega)
      rw [e24, e32]
      obtain ⟨hr24, hr32⟩ := hTr.2.2 hws_nz
      refine ⟨hr24, fun htS i hi => ?_⟩
      have hne32 := hno_ws32 hws_nz
      have hu32 := hu_other _ htS hne32
      have hwf32 := (hT.2.1 _ htS).1
      have hvals_eq := htabValues_eq_of_unhit hwf32 hu32
      obtain ⟨hhdr32, _⟩ := hother_fp _ htS hne32
      rw [hhdr32 3 (by omega)] at hi
      have hget : (htabValues post (memW s (globN s "ws" + 32)))[i]? =
          (htabValues s (memW s (globN s "ws" + 32)))[i]? := by rw [hvals_eq]
      simp only [htabValues, List.getElem?_map, List.getElem?_range, hhdr32 3 (by omega), hi,
        Option.map_some, Option.some.injEq] at hget
      rw [hget]; exact hr32 htS i hi
  refine ⟨S, Nd, fun _ h => h, ⟨hT_post, hJ_post, hF_post, hTr_post⟩, ?_, ?_, trivial⟩
  · intro o ho
    unfold worldOwned at ho
    rcases List.mem_append.1 ho with ho12 | ho_nd
    · rcases List.mem_append.1 ho12 with ho_tab | ho_fix
      · obtain ⟨u, hu, hi⟩ := List.mem_flatMap.1 ho_tab
        by_cases hu0 : u = t0
        · subst hu0
          rcases (hfp_t0 o hi).2 with ⟨j, hj, hin⟩ | hfresh
          · refine Or.inr (Or.inl ⟨j, ?_, hin⟩)
            unfold worldOwned
            exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨u, hu, hj⟩))
          · exact Or.inr (Or.inr ⟨hfresh.1, by have := hfresh.2; omega⟩)
        · rw [(hother_fp u hu hu0).2] at hi
          refine Or.inr (Or.inl ⟨o, ?_, le_rfl, le_rfl⟩)
          unfold worldOwned
          exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨u, hu, hi⟩))
      · rw [hfix_eq] at ho_fix
        refine Or.inr (Or.inl ⟨o, ?_, le_rfl, le_rfl⟩)
        unfold worldOwned
        exact List.mem_append_left _ (List.mem_append_right _ ho_fix)
    · rw [hne_eq] at ho_nd
      refine Or.inr (Or.inl ⟨o, ?_, le_rfl, le_rfl⟩)
      unfold worldOwned
      exact List.mem_append_right _ ho_nd
  · intro a hkeep hnot_hf
    apply hfr a
    · intro j hj
      apply hkeep j
      apply List.mem_append_left; apply List.mem_append_left
      unfold worldOwned
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨t0, ht0_S, hj⟩))
    · intro hcf
      apply hnot_hf
      obtain ⟨h1, h2⟩ := hcf
      unfold heapFree CellHits at *
      dsimp at h1 h2 ⊢
      have := hAp.2.2.1
      omega

/-- One-line `ProgWStep` combinator for `htab_set(lds 1 (rec + off), kExp, vExp)` on any
non-value world table slot `(rec, off, roleName)` (such as `("bs", 72, "bs+72")`,
`("ts", 8, "ts+8")`, `("ts", 24, "ts+24")`, `("ts", 40, "ts+40")`, `("ts", 56, "ts+56")`). -/
theorem progWStep_call0_htab_set_recSlot {B : BufList} {gw : List String}
    (recName roleName : String) (off : BitVec 64)
    (kExp vExp : ExpHOL 64)
    (hhp_in : "heap_ptr" ∈ gw)
    (hoff_lt : off.toNat < sourceBase)
    (hslot_nonVal : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat),
      TablesTyped s S → globN s recName ≠ 0 → memW s (globN s recName + off.toNat) ≠ 0 →
      memW s (globN s recName + off.toNat) ∈ S ∧
      (globN s "bs" ≠ 0 → memW s (globN s "bs" + 32) ≠ memW s (globN s recName + off.toNat)) ∧
      (globN s "ts" ≠ 0 → memW s (globN s "ts" + 32) ≠ memW s (globN s recName + off.toNat)) ∧
      globN s "bal_accounts" ≠ memW s (globN s recName + off.toNat) ∧
      (∀ ad ∈ balRecords s, memW s ad ≠ memW s (globN s recName + off.toNat)) ∧
      (globN s "ws" ≠ 0 → memW s (globN s "ws" + 32) ≠ memW s (globN s recName + off.toNat))) :
    ProgWStep B gw
      (.call (some (none, none)) (ofString "htab_set")
        [.load .one (.op .add [.var .global (ofString recName), .const off]), kExp, vExp]) := by
  have _ := roleName
  intro F s hcode hW hnt hfr
  set argsL : List (ExpHOL 64) :=
    [.load .one (.op .add [.var .global (ofString recName), .const off]), kExp, vExp]
  rw [evaluateHOLFiniteState_call] at hnt hfr ⊢
  rcases hargs : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) argsL with _ | values
  · simp [evalListHOLFinite, hargs] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [evalListHOLFinite, hargs] at hnt hfr ⊢
    have hargs_fin : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) argsL = some values := by
      rwa [evalListHOLFinite_eq_toExact]
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "htab_set") values with _ | ⟨body', callee, ret'⟩
    · simp [hl] at hfr; exact absurd hfr not_flowingOrResumes_error
    · simp only [hl] at hnt hfr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · rw [if_neg hz] at hnt hfr ⊢
        obtain ⟨v1, _, _, he1, _, _, hc_t, _, _⟩ := callee_param_three s (ofString "htab_set")
          (ofString "t") (ofString "key") (ofString "value") .one .one .one _ _
          (by rw [hcode]; exact EvmFrameSpecs.lookup_htab_set) _ _ _ values body' callee ret' hargs_fin hl
        obtain ⟨tw, rfl, htw_nat, hrec_nz⟩ := evalAt_loadG_nz s hW.1.1 recName off hoff_lt v1 he1
        have hloc_t : locN (callEntryStateHOLFinite s callee) "t" = memW s (globN s recName + off.toNat) := by
          simp [locN, callEntryStateHOLFinite, hc_t, htw_nat]
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨res, post⟩
        simp only [hrun] at hnt hfr ⊢
        have hbe_post : post.be = s.be := by
          have inv := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body').2.2.1
          rw [hrun] at inv; exact inv
        cases res with
        | none => exact absurd hfr not_flowingOrResumes_error
        | some cr =>
          cases cr with
          | timeOut => simp at hnt
          | error | «break» | «continue» => exact absurd hfr not_flowingOrResumes_error
          | finalFfi _ => exact absurd hfr not_flowingOrResumes_finalFfi
          | exception eid ev =>
            exfalso
            have hne : eid ≠ ofString "TrapErr" := by
              rcases hfr with h | h | h | ⟨_, h⟩ | ⟨e', v', h, hne⟩ <;> try simp at h
              obtain ⟨rfl, _⟩ := h; exact hne
            have hbody_ok : noCatchableRaise trapOnlyCallees body' = true :=
              trapOnlyCallees_good (ofString "htab_set") (by decide) values body' callee ret' (by rwa [← hcode])
            have hno := evaluate_noCatchableRaise trapOnlyCallees trapOnlyCallees_good
              body' hbody_ok (callEntryStateHOLFinite s callee) hcode eid ev hne
            rw [hrun] at hno; exact hno rfl
          | returned v =>
            dsimp only at hfr ⊢
            split
            · have hnz_at := FunSpec.at_lookup EvmFrameSpecs.nz_htab_set s hcode values body' callee ret' hl
                (guestInv_callEntry s callee hW.1.1) (by rw [hrun]; simp)
              rw [hrun] at hnz_at
              have ht0_nz : memW s (globN s recName + off.toNat) ≠ 0 := by
                rw [← hloc_t]; exact hnz_at (Or.inl ⟨v, rfl⟩)
              have hArgWF : HtabArgWF (callEntryStateHOLFinite s callee) := by
                obtain ⟨hAs, S, hT, _⟩ := hW
                have ht0_S := (hslot_nonVal s S hT hrec_nz ht0_nz).1
                refine ⟨localsFree_arenaReady s _ _ hAs, ?_, ?_⟩
                · rw [hloc_t]; exact (htabWF_with_locals s callee (s.clock - 1) _).2 (hT.2.1 _ ht0_S).1
                · rw [hloc_t]; exact fun i hi => ((hT.2.1 _ ht0_S).2 i hi).1
              have hexit := FunSpec.at_lookup htab_set_spec s hcode values body' callee ret' hl
                hArgWF (by rw [hrun]; simp)
              rw [hrun] at hexit
              have hex := hexit v rfl
              dsimp only [HtabExit] at hex
              rw [hloc_t] at hex
              change let t := memW s (globN s recName + off.toNat)
                let fresh : Ivl := (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr")
                ArenaReady post ∧ HtabWF post t ∧ hdr post t 0 = hdr s t 0 ∧ hdr post t 1 = hdr s t 1 ∧
                globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
                (∀ i ∈ htabFootprint post t, Allocated post i ∧
                  ((∃ j ∈ htabFootprint s t, Inside i j.1 (j.1 + j.2)) ∨ Inside i fresh.1 (fresh.1 + fresh.2))) ∧
                FrameOutside s post (htabFootprint s t) fresh ∧
                (∀ k : MlS, k ∉ (["heap_ptr"] : List String).map ofString →
                  s.globals.lookup k = post.globals.lookup k) at hex
              obtain ⟨hAp, hwf_t0, hh0, _, hhp, hfp_t0, hfr_t0, hg_t0⟩ := hex
              have hstep0 : WorldStepSc (bufRegions []) ["heap_ptr"] stdKeep NoExtra s none post :=
                worldStepSc_of_htabExit_nonValue hW hbe_post hg_t0 hg_t0
                  (fun S hT => hslot_nonVal s S hT hrec_nz ht0_nz)
                  hAp hwf_t0 hh0 hhp hfp_t0 hfr_t0
              exact (hstep0.with_locals_clock s.locals post.clock).mono_bufs
                (fun _ h => by cases h)
                (fun g hg => by simp at hg; subst hg; exact hhp_in)
            · rename_i hbad; simp [hbad] at hfr; exact absurd hfr not_flowingOrResumes_error

end InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs

