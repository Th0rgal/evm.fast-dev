import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkDhiWorldEffTop

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.style.nameCheck false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk

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
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8GuestInv.Fast_C08WkShard03

theorem lookup_ssz_fixed_list_count_dhi :
    originalRuntimeCode.lookup (ofString "ssz_fixed_list_count") =
      some ([(ofString "len", .one), (ofString "sz", .one), (ofString "lim", .one)],
        sourceFnBody Guest.Software.guestFn_ssz_fixed_list_count, .one) :=
  lookup_of_guestAst_getElem 203 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_ssz_fixed_list_count) rfl

theorem ssz_offs_allocated_strong {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hWOK : WorldOK s) :
    globN s "ssz_offs" = 0 ∨
    Allocated s (globN s "ssz_offs", 64) := by
  obtain ⟨hAs, S, hWS⟩ := hWOK
  obtain ⟨Nd, hWT⟩ := (worldTyped_iff_with s S).1 hWS
  have hmem : bufferRegion s ("ssz_offs", 64) ∈ fixedObjects s := by
    unfold fixedObjects
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    exact List.mem_map.2 ⟨("ssz_offs", 64), by decide, rfl⟩
  rcases hWT.2.2.1.1 _ hmem with hz | ⟨hal, _⟩
  · by_cases hg0 : globN s "ssz_offs" = 0
    · exact Or.inl hg0
    · simp [bufferRegion, hg0] at hz
  · by_cases hg0 : globN s "ssz_offs" = 0
    · exact Or.inl hg0
    · simp only [bufferRegion, hg0, ↓reduceIte] at hal
      exact Or.inr hal

theorem lookupCode_two_words_any_dhi
    {lk : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)}
    {fname p1 p2 : MlS} {body : ProgHOL 64} {retShape : ShapeHOL}
    {vals : List (ValueHOL 64)} {L : HolFiniteMapExact MlS (ValueHOL 64)}
    (hne : p1 ≠ p2)
    (hlook : lk fname = some ([(p1, .one), (p2, .one)], body, retShape))
    (hl : lookupCodeHOLFinite lk fname vals = some (body, L, retShape)) :
    ∃ w1 w2 : BitVec 64,
      vals = [.val (.word w1), .val (.word w2)] ∧
      L.lookup p1 = some (.val (.word w1)) ∧
      L.lookup p2 = some (.val (.word w2)) := by
  have hx := lookupCodeHOLFinite_eq_some lk fname vals body L retShape hl
  simp only [lookupCodeHOLExact, hlook] at hx
  rcases vals with _ | ⟨v1, _ | ⟨v2, _ | _⟩⟩
  · simp at hx
  · simp at hx
  · rcases v1 with ⟨⟨w1⟩⟩ | _ | _ <;> rcases v2 with ⟨⟨w2⟩⟩ | _ | _ <;>
      simp [shapeOfHOLExact, shapeEqHOL] at hx
    obtain ⟨_, hL⟩ := hx
    refine ⟨w1, w2, rfl, ?_, ?_⟩ <;>
      (rw [← hL]; simp only [HolFiniteMapExact.lookup_updateList, HolFiniteMapExact.lookup_empty,
        FUPDATE_LIST, FUPDATE, List.foldl, hne, Ne.symm hne, ↓reduceIte])
  · simp at hx

theorem lookupCode_three_words_any_dhi
    {lk : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)}
    {fname p1 p2 p3 : MlS} {body : ProgHOL 64} {retShape : ShapeHOL}
    {vals : List (ValueHOL 64)} {L : HolFiniteMapExact MlS (ValueHOL 64)}
    (hne12 : p1 ≠ p2) (hne13 : p1 ≠ p3) (hne23 : p2 ≠ p3)
    (hlook : lk fname = some ([(p1, .one), (p2, .one), (p3, .one)], body, retShape))
    (hl : lookupCodeHOLFinite lk fname vals = some (body, L, retShape)) :
    ∃ w1 w2 w3 : BitVec 64,
      vals = [.val (.word w1), .val (.word w2), .val (.word w3)] ∧
      L.lookup p1 = some (.val (.word w1)) ∧
      L.lookup p2 = some (.val (.word w2)) ∧
      L.lookup p3 = some (.val (.word w3)) := by
  have hx := lookupCodeHOLFinite_eq_some lk fname vals body L retShape hl
  simp only [lookupCodeHOLExact, hlook] at hx
  rcases vals with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | _⟩⟩⟩
  · simp at hx
  · simp at hx
  · simp at hx
  · rcases v1 with ⟨⟨w1⟩⟩ | _ | _ <;> rcases v2 with ⟨⟨w2⟩⟩ | _ | _ <;> rcases v3 with ⟨⟨w3⟩⟩ | _ | _ <;>
      simp [shapeOfHOLExact, shapeEqHOL] at hx
    obtain ⟨_, hL⟩ := hx
    refine ⟨w1, w2, w3, rfl, ?_, ?_, ?_⟩ <;>
      (rw [← hL]; simp only [HolFiniteMapExact.lookup_updateList, HolFiniteMapExact.lookup_empty,
        FUPDATE_LIST, FUPDATE, List.foldl, hne12, hne13, hne23, Ne.symm hne12, Ne.symm hne13, Ne.symm hne23, ↓reduceIte])
  · simp at hx

theorem lookupCode_four_words_any_dhi
    {lk : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)}
    {fname p1 p2 p3 p4 : MlS} {body : ProgHOL 64} {retShape : ShapeHOL}
    {vals : List (ValueHOL 64)} {L : HolFiniteMapExact MlS (ValueHOL 64)}
    (hne12 : p1 ≠ p2) (hne13 : p1 ≠ p3) (hne14 : p1 ≠ p4)
    (hne23 : p2 ≠ p3) (hne24 : p2 ≠ p4) (hne34 : p3 ≠ p4)
    (hlook : lk fname = some ([(p1, .one), (p2, .one), (p3, .one), (p4, .one)], body, retShape))
    (hl : lookupCodeHOLFinite lk fname vals = some (body, L, retShape)) :
    ∃ w1 w2 w3 w4 : BitVec 64,
      vals = [.val (.word w1), .val (.word w2), .val (.word w3), .val (.word w4)] ∧
      L.lookup p1 = some (.val (.word w1)) ∧
      L.lookup p2 = some (.val (.word w2)) ∧
      L.lookup p3 = some (.val (.word w3)) ∧
      L.lookup p4 = some (.val (.word w4)) := by
  have hx := lookupCodeHOLFinite_eq_some lk fname vals body L retShape hl
  simp only [lookupCodeHOLExact, hlook] at hx
  rcases vals with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | ⟨v4, _ | _⟩⟩⟩⟩
  · simp at hx
  · simp at hx
  · simp at hx
  · simp at hx
  · rcases v1 with ⟨⟨w1⟩⟩ | _ | _ <;> rcases v2 with ⟨⟨w2⟩⟩ | _ | _ <;>
      rcases v3 with ⟨⟨w3⟩⟩ | _ | _ <;> rcases v4 with ⟨⟨w4⟩⟩ | _ | _ <;>
      simp [shapeOfHOLExact, shapeEqHOL] at hx
    obtain ⟨_, hL⟩ := hx
    refine ⟨w1, w2, w3, w4, rfl, ?_, ?_, ?_, ?_⟩ <;>
      (rw [← hL]; simp only [HolFiniteMapExact.lookup_updateList, HolFiniteMapExact.lookup_empty,
        FUPDATE_LIST, FUPDATE, List.foldl, hne12, hne13, hne14, hne23, hne24, hne34,
        Ne.symm hne12, Ne.symm hne13, Ne.symm hne14, Ne.symm hne23, Ne.symm hne24, Ne.symm hne34, ↓reduceIte])
  · simp at hx

theorem call0_noret_dhi {F : Type} (u : PanSemStateFiniteExact 64 F)
    (fn : MlS) (args : List (ExpHOL 64)) :
    ∀ rv, (evaluateHOLFiniteState u (.call (some (none, none)) fn args)).1 ≠ some (.returned rv) := by
  intro rv
  rw [evaluateHOLFiniteState_call]
  rcases evalListHOLFinite u (h := fun a => Classical.propDecidable (u.memaddrs a)) args with _ | vals
  · simp
  · dsimp only
    rcases lookupCodeHOLFinite u.code.lookup fn vals with _ | ⟨body, callee, rs⟩
    · simp
    · dsimp only
      split
      · simp
      · rcases evaluateHOLFiniteState (callEntryStateHOLFinite u callee) body with ⟨r, st⟩
        cases r with
        | none => simp
        | some r1 =>
          cases r1 with
          | returned _ => dsimp only; split <;> simp
          | _ => simp

theorem ite_call0_noret_dhi {F : Type} (u : PanSemStateFiniteExact 64 F)
    (cond : ExpHOL 64) (fn : MlS) (args : List (ExpHOL 64)) :
    ∀ rv, (evaluateHOLFiniteState u (.ite cond (.call (some (none, none)) fn args) .skip)).1 ≠ some (.returned rv) := by
  intro rv
  rw [evaluateHOLFiniteState_ite]
  rcases @evalHOLExact 64 F _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a)) cond with _ | cv
  · simp
  · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> try simp
    by_cases h0 : cw = 0#64
    · subst h0; simp [evaluateHOLFiniteState_skip]
    · rw [if_neg h0]; exact call0_noret_dhi u fn args rv

theorem call0_nobreak_nock_dhi {F : Type} (u : PanSemStateFiniteExact 64 F)
    (fn : MlS) (args : List (ExpHOL 64)) :
    (evaluateHOLFiniteState u (.call (some (none, none)) fn args)).1 ≠ some .break ∧
    (evaluateHOLFiniteState u (.call (some (none, none)) fn args)).1 ≠ some .continue := by
  constructor <;> {
    rw [evaluateHOLFiniteState_call]
    rcases evalListHOLFinite u (h := fun a => Classical.propDecidable (u.memaddrs a)) args with _ | vals
    · simp
    · dsimp only
      rcases lookupCodeHOLFinite u.code.lookup fn vals with _ | ⟨body, callee, rs⟩
      · simp
      · dsimp only
        split
        · simp
        · rcases evaluateHOLFiniteState (callEntryStateHOLFinite u callee) body with ⟨r, st⟩
          cases r with
          | none => simp
          | some r1 =>
            cases r1 with
            | returned _ => dsimp only; split <;> simp
            | _ => simp
  }

theorem ite_call0_nobreak_dhi {F : Type} (u : PanSemStateFiniteExact 64 F)
    (cond : ExpHOL 64) (fn : MlS) (args : List (ExpHOL 64)) :
    (evaluateHOLFiniteState u (.ite cond (.call (some (none, none)) fn args) .skip)).1 ≠ some .break ∧
    (evaluateHOLFiniteState u (.ite cond (.call (some (none, none)) fn args) .skip)).1 ≠ some .continue := by
  constructor <;> {
    rw [evaluateHOLFiniteState_ite]
    rcases @evalHOLExact 64 F _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a)) cond with _ | cv
    · simp
    · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> try simp
      by_cases h0 : cw = 0#64
      · subst h0; simp [evaluateHOLFiniteState_skip]
      · rw [if_neg h0]
        first
        | exact (call0_nobreak_nock_dhi u fn args).1
        | exact (call0_nobreak_nock_dhi u fn args).2
  }

theorem ite2_call0_noctrl_dhi {F : Type} (u : PanSemStateFiniteExact 64 F)
    (c1 c2 : ExpHOL 64) (fn : MlS) (args : List (ExpHOL 64)) :
    (∀ rv, (evaluateHOLFiniteState u (.ite c1 (.ite c2 (.call (some (none, none)) fn args) .skip) .skip)).1 ≠ some (.returned rv)) ∧
    (evaluateHOLFiniteState u (.ite c1 (.ite c2 (.call (some (none, none)) fn args) .skip) .skip)).1 ≠ some .break ∧
    (evaluateHOLFiniteState u (.ite c1 (.ite c2 (.call (some (none, none)) fn args) .skip) .skip)).1 ≠ some .continue := by
  have h1 := ite_call0_noret_dhi u c2 fn args
  have h2 := ite_call0_nobreak_dhi u c2 fn args
  rw [evaluateHOLFiniteState_ite, evaluateHOLFiniteState_skip] at h1 h2
  refine ⟨fun rv => ?_, ?_, ?_⟩
  · rw [evaluateHOLFiniteState_ite]
    rcases @evalHOLExact 64 F _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a)) c1 with _ | cv
    · simp
    · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> try simp
      by_cases h0 : cw = 0#64
      · subst h0; simp [evaluateHOLFiniteState_skip]
      · rw [if_neg h0]; exact h1 rv
  · rw [evaluateHOLFiniteState_ite]
    rcases @evalHOLExact 64 F _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a)) c1 with _ | cv
    · simp
    · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> try simp
      by_cases h0 : cw = 0#64
      · subst h0; simp [evaluateHOLFiniteState_skip]
      · rw [if_neg h0]; exact h2.1
  · rw [evaluateHOLFiniteState_ite]
    rcases @evalHOLExact 64 F _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a)) c1 with _ | cv
    · simp
    · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> try simp
      by_cases h0 : cw = 0#64
      · subst h0; simp [evaluateHOLFiniteState_skip]
      · rw [if_neg h0]; exact h2.2

theorem ite2_ssz_fail_none_keeps {F : Type} (u sb : PanSemStateFiniteExact 64 F)
    (hcode : u.code = originalRuntimeCode)
    (c1 c2 : ExpHOL 64) (code_arg : ExpHOL 64)
    (h : evaluateHOLFiniteState u (.ite c1 (.ite c2 (.call (some (none, none)) (ofString "ssz_fail") [code_arg]) .skip) .skip) = (none, sb)) :
    sb = u := by
  have hk := ite_ssz_fail_keeps u sb hcode c2 code_arg
  rw [evaluateHOLFiniteState_ite, evaluateHOLFiniteState_skip] at hk
  have h1 : evaluateHOLFiniteState u (.ite c1 (.ite c2 (.call (some (none, none)) (ofString "ssz_fail") [code_arg]) .skip) .skip) = (none, sb) := h
  revert h1
  rw [evaluateHOLFiniteState_ite]
  rcases @evalHOLExact 64 F _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a)) c1 with _ | cv
  · simp
  · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> try simp
    by_cases h0 : cw = 0#64
    · subst h0; simp [evaluateHOLFiniteState_skip]
      intro h; exact h.symm
    · rw [if_neg h0]
      intro h; exact (hk h).1

def DhiOffsOK {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  ArenaReady s ∧
  (globN s "ssz_offs" = 0 ∨
   (sourceBase ≤ globN s "ssz_offs" ∧ globN s "ssz_offs" + 64 ≤ heapEnd ∧
    globN s "ssz_offs" % 8 = 0 ∧
    ((sourceBase ≤ globN s "ssz_offs" ∧ globN s "ssz_offs" + 64 ≤ globN s "heap_ptr") ∨
     (scratchStart ≤ globN s "ssz_offs" ∧ globN s "ssz_offs" + 64 ≤ scratchEnd))))

theorem dhiOffsOK_of_worldOK {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hWOK : WorldOK s) : DhiOffsOK s := by
  refine ⟨hWOK.1, ?_⟩
  rcases ssz_offs_allocated_strong hWOK with h0 | hal
  · exact Or.inl h0
  · rcases ssz_offs_allocated hWOK with h0' | ⟨hlo, hhi, hmod, _⟩
    · exact Or.inl h0'
    · refine Or.inr ⟨hlo, hhi, hmod, ?_⟩
      rcases hal with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, h2⟩
      · have hfmp_lo : scratchStart ≤ globN s "frame_mem_ptr" := hWOK.1.2.2.2.1
        have hfmp_sp : globN s "frame_mem_ptr" ≤ globN s "scratch_ptr" := hWOK.1.2.2.2.2.1
        exact Or.inr ⟨by omega, h2⟩

theorem dhiOffsOK_of_worldEff {F : Type}
    {s cur : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {B : List (String × Nat)}
    (hOK : DhiOffsOK s)
    (heff : WorldEff s cur Rl B dhiGw) : DhiOffsOK cur := by
  refine ⟨heff.arena, ?_⟩
  have hg : globN cur "ssz_offs" = globN s "ssz_offs" :=
    globN_eq_of_lookup (heff.gw_kept (ofString "ssz_offs") (by decide))
  have hhp : globN s "heap_ptr" ≤ globN cur "heap_ptr" := heff.hp_lo
  rw [hg]
  rcases hOK.2 with h0 | ⟨hlo, hhi, hmod, hal⟩
  · exact Or.inl h0
  · refine Or.inr ⟨hlo, hhi, hmod, ?_⟩
    rcases hal with ⟨h1, h2⟩ | hsc
    · exact Or.inl ⟨h1, Nat.le_trans h2 hhp⟩
    · exact Or.inr hsc

theorem dhiOffsOK_locals_clock {F : Type}
    {s : PanSemStateFiniteExact 64 F}
    (hOK : DhiOffsOK s) (hc : s.code = originalRuntimeCode)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (c : Nat) :
    DhiOffsOK { s with locals := L, clock := c } := by
  have heff : WorldEff s { s with locals := L, clock := c } [] [] dhiGw :=
    (WorldEff.refl s [] [] dhiGw hOK.1 hc).locals_clock L c
  exact dhiOffsOK_of_worldEff hOK heff

theorem worldEff_store_ssz_offs_const_ok {F : Type}
    {s cur : PanSemStateFiniteExact 64 F} {B : List (String × Nat)}
    (hOK : DhiOffsOK s)
    (heff : WorldEff s cur (dhiOffsRegions s) B dhiGw)
    (off : Nat) (hoff : off + 8 ≤ 64)
    (dstExp valExp : ExpHOL 64)
    (hdst : dstExp = .var .global (ofString "ssz_offs") ∧ off = 0 ∨
      dstExp = .op .add [.var .global (ofString "ssz_offs"), .const (BitVec.ofNat 64 off)])
    (hval_one : ∀ v, @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) valExp =
      some v → ∃ w : BitVec 64, v = .val (.word w)) :
    WorldEff s (evaluateHOLFiniteState cur (.store dstExp valExp)).2 (dhiOffsRegions s) B dhiGw := by
  refine worldEff_store_word heff dstExp valExp hval_one (fun x hx hdom => ?_)
  have hg_kept := heff.gw_kept (ofString "ssz_offs") (by decide)
  obtain ⟨sw, hsw_s⟩ := hOK.1.2.2.2.2.2.2.2.2.2 "ssz_offs" (by decide)
  have hsw_cur : cur.globals.lookup (ofString "ssz_offs") = some (.val (.word sw)) :=
    hg_kept.symm.trans hsw_s
  have hglob : globN s "ssz_offs" = sw.toNat := by unfold GlobalWord at hsw_s; simp [globN, hsw_s]
  have hx_eq : x = sw + BitVec.ofNat 64 off := by
    rcases hdst with ⟨rfl, rfl⟩ | rfl
    · simp [evalHOLExact, toExact, hsw_cur] at hx
      simpa using hx.symm
    · simp [evalHOLExact, evalListHOLExact, toExact, hsw_cur, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
      exact hx.symm
  rw [heff.memaddrs, hOK.1.1.memaddrs, ordinaryDomain_iff] at hdom
  rcases hOK.2 with hg0 | ⟨hlo, hhi, _, _⟩
  · have hsw0 : sw = 0#64 := BitVec.eq_of_toNat_eq (by simp; omega)
    subst hsw0 hx_eq
    have hsb : 64 < sourceBase := by decide
    have h1 : (0#64 + BitVec.ofNat 64 off).toNat = off := by
      simp [BitVec.toNat_ofNat]; omega
    omega
  · have hhe : heapEnd < 2 ^ 64 := by decide
    have hsb : 0 < sourceBase := by decide
    have hg_ne0 : globN s "ssz_offs" ≠ 0 := by omega
    have hx_nat : x.toNat = globN s "ssz_offs" + off := by
      rw [hx_eq, BitVec.toNat_add_of_lt]
      · simp [hglob, BitVec.toNat_ofNat]; omega
      · simp [BitVec.toNat_ofNat]; omega
    exact Or.inl ⟨(globN s "ssz_offs", if globN s "ssz_offs" = 0 then 0 else 64),
      List.mem_singleton.2 rfl, by simp [hg_ne0]; omega, by simp [hg_ne0]; omega⟩

theorem worldEff_store_ssz_offs_dyn_ok {F : Type}
    {s cur : PanSemStateFiniteExact 64 F} {B : List (String × Nat)}
    (hOK : DhiOffsOK s)
    (heff : WorldEff s cur (dhiOffsRegions s) B dhiGw)
    (offExp valExp : ExpHOL 64)
    (offw : BitVec 64)
    (hoff_ev : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) offExp =
      some (.val (.word offw)))
    (hoff_le : offw.toNat + 8 ≤ 64)
    (hval_one : ∀ v, @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) valExp =
      some v → ∃ w : BitVec 64, v = .val (.word w)) :
    WorldEff s (evaluateHOLFiniteState cur (.store (.op .add [.var .global (ofString "ssz_offs"), offExp]) valExp)).2
      (dhiOffsRegions s) B dhiGw := by
  refine worldEff_store_word heff _ valExp hval_one (fun x hx hdom => ?_)
  have hg_kept := heff.gw_kept (ofString "ssz_offs") (by decide)
  obtain ⟨sw, hsw_s⟩ := hOK.1.2.2.2.2.2.2.2.2.2 "ssz_offs" (by decide)
  have hsw_cur : cur.globals.lookup (ofString "ssz_offs") = some (.val (.word sw)) :=
    hg_kept.symm.trans hsw_s
  have hglob : globN s "ssz_offs" = sw.toNat := by unfold GlobalWord at hsw_s; simp [globN, hsw_s]
  have hx_eq : x = sw + offw := by
    simp [evalHOLExact, evalListHOLExact, toExact, hsw_cur, hoff_ev, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
    exact hx.symm
  rw [heff.memaddrs, hOK.1.1.memaddrs, ordinaryDomain_iff] at hdom
  rcases hOK.2 with hg0 | ⟨hlo, hhi, _, _⟩
  · have hsw0 : sw = 0#64 := BitVec.eq_of_toNat_eq (by simp; omega)
    subst hsw0 hx_eq
    have hsb : 64 < sourceBase := by decide
    have h1 : (0#64 + offw).toNat = offw.toNat := by simp
    omega
  · have hhe : heapEnd < 2 ^ 64 := by decide
    have hsb : 0 < sourceBase := by decide
    have hg_ne0 : globN s "ssz_offs" ≠ 0 := by omega
    have hx_nat : x.toNat = globN s "ssz_offs" + offw.toNat := by
      rw [hx_eq, BitVec.toNat_add_of_lt] <;> omega
    exact Or.inl ⟨(globN s "ssz_offs", if globN s "ssz_offs" = 0 then 0 else 64),
      List.mem_singleton.2 rfl, by simp [hg_ne0]; omega, by simp [hg_ne0]; omega⟩

theorem dhiOffs_disj_above_heap {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hWOK : WorldOK s) {addr : Nat}
    (hlo : globN s "heap_ptr" ≤ addr)
    (hhi_lim : addr + 8 ≤ heapLimit) :
    ∀ iv ∈ dhiOffsRegions s, 0 < iv.2 → ¬ (iv.1 ≤ addr ∧ addr + 8 ≤ iv.1 + iv.2 ∨ addr < iv.1 + iv.2 ∧ iv.1 < addr + 8) := by
  intro iv hiv hpos hhit
  simp only [dhiOffsRegions, List.mem_singleton] at hiv
  subst hiv
  by_cases hg0 : globN s "ssz_offs" = 0
  · simp [hg0] at hpos
  · simp only [hg0, ↓reduceIte] at hpos hhit
    rcases ssz_offs_allocated_strong hWOK with h0 | hal
    · exact hg0 h0
    · rcases hal with ⟨_, hhi⟩ | ⟨hsc, _⟩
      · omega
      · have hfmp_lo : scratchStart ≤ globN s "frame_mem_ptr" := hWOK.1.2.2.2.1
        have hfmp_sp : globN s "frame_mem_ptr" ≤ globN s "scratch_ptr" := hWOK.1.2.2.2.2.1
        have hlim_sc : heapLimit ≤ scratchStart := by decide
        omega

theorem worldEff_dhi_keeps_heap_memW {F : Type}
    {s cur next : PanSemStateFiniteExact 64 F}
    (hWOK_s : WorldOK s)
    (heff_s_cur : WorldEff s cur (dhiOffsRegions s) ([] : List (String × Nat)) dhiGw)
    (heff_step : WorldEff cur next (dhiOffsRegions cur) ([] : List (String × Nat)) dhiGw)
    {addr : Nat}
    (hal8 : addr % 8 = 0)
    (hlo : globN s "heap_ptr" ≤ addr)
    (hhi : addr + 8 ≤ globN cur "heap_ptr") :
    memW next addr = memW cur addr := by
  have hcur_hp_lim : globN cur "heap_ptr" ≤ heapLimit := heff_s_cur.arena.2.2.1
  have hhl_lt : heapLimit < 2 ^ 64 := by decide
  have ha_lt : addr < 2 ^ 64 := by omega
  have hbv_nat : (BitVec.ofNat 64 addr).toNat = addr := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]
  have hoff_eq : dhiOffsRegions cur = dhiOffsRegions s := by
    have hg := globN_eq_of_lookup (heff_s_cur.gw_kept (ofString "ssz_offs") (by decide))
    simp [dhiOffsRegions, hg]
  unfold memW
  by_cases hmem : next.memory (BitVec.ofNat 64 addr) = cur.memory (BitVec.ofNat 64 addr)
  · rw [hmem]
  · exfalso
    rcases heff_step.cell_frame (BitVec.ofNat 64 addr) hmem with ⟨iv, hiv, hpos, hc1, hc2⟩ | ⟨_, hgs, _⟩ | ⟨_, hfg1, _⟩ | ⟨_, hhf1, _⟩
    · rw [hoff_eq] at hiv
      exact dhiOffs_disj_above_heap hWOK_s hlo (by omega) iv hiv hpos (Or.inr ⟨by omega, by omega⟩)
    · cases hgs
    · dsimp only [freeGap] at hfg1
      have hfmp_lo : scratchStart ≤ globN cur "frame_mem_ptr" := heff_s_cur.arena.2.2.2.1
      have hlim_sc : heapLimit ≤ scratchStart := by decide
      omega
    · dsimp only [heapFree] at hhf1
      omega

theorem store_memW_eq_and_ne {F : Type}
    (cur mid : PanSemStateFiniteExact 64 F) (dstExp valExp : ExpHOL 64)
    (xw vw : BitVec 64)
    (hrun : evaluateHOLFiniteState cur (.store dstExp valExp) = (none, mid))
    (hdst : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) dstExp = some (.val (.word xw)))
    (hval : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) valExp = some (.val (.word vw))) :
    memW mid xw.toNat = vw.toNat ∧
    (∀ y : Nat, y < 2 ^ 64 → y ≠ xw.toNat → memW mid y = memW cur y) := by
  rw [evaluateHOLFiniteState_store] at hrun
  simp only [hdst, hval, flattenHOL, panMemStoresHOL, panMemStoreHOL] at hrun
  by_cases hdom : cur.memaddrs xw
  · simp only [hdom, ↓reduceIte] at hrun
    injection hrun with _ hmid
    subst hmid
    refine ⟨?_, fun y hy hne => ?_⟩
    · unfold memW; dsimp only
      have hbx : BitVec.ofNat 64 xw.toNat = xw := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt xw.isLt]
      simp [hbx]
    · unfold memW; dsimp only
      have hby : BitVec.ofNat 64 y ≠ xw := by
        intro heq; apply hne
        have h1 := congrArg BitVec.toNat heq
        rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hy] at h1
      simp [hby]
  · simp only [hdom, ↓reduceIte] at hrun
    simp at hrun

theorem wordsOK_preserved_of_worldEff {F : Type}
    {cur next : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (heff : WorldEff cur next Rl B gw)
    {iv : Ivl}
    (hal8 : iv.1 % 8 = 0) (hsz8 : iv.2 % 8 = 0)
    (hlo : sourceBase ≤ iv.1) (hhi : iv.1 + iv.2 ≤ heapLimit) :
    WordsOK next iv := by
  have hle : heapLimit ≤ heapEnd := by decide
  exact wordsOK_of_inside_heap heff.arena.1 hal8 hsz8 hlo (Nat.le_trans hhi hle)

theorem ssz_fixed_list_count_body_returns {F : Type}
    (ent : PanSemStateFiniteExact 64 F) (wlen wsz wlim : BitVec 64)
    (hcode : ent.code = originalRuntimeCode)
    (hG : GuestInv ent)
    (hlen : ent.locals.lookup (ofString "len") = some (.val (.word wlen)))
    (hsz : ent.locals.lookup (ofString "sz") = some (.val (.word wsz)))
    (hlim : ent.locals.lookup (ofString "lim") = some (.val (.word wlim)))
    (rv : ValueHOL 64) (cpost : PanSemStateFiniteExact 64 F)
    (hrun : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_ssz_fixed_list_count) =
      (some (.returned rv), cpost)) :
    0 < wsz.toNat ∧
    ∃ qw : BitVec 64,
      rv = .val (.word qw) ∧
      qw.toNat * wsz.toNat = wlen.toNat ∧
      qw.toNat ≤ wlim.toNat := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_ssz_fixed_list_count,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
    Option.map, List.map] at hrun
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hrun
  have hargs : evalListHOLFinite ent (h := fun a => Classical.propDecidable (ent.memaddrs a))
      [.var .local (ofString "len"), .var .local (ofString "sz")] =
      some [.val (.word wlen), .val (.word wsz)] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact, evalHOLExact, toExact, hlen, hsz]
  rw [hargs] at hrun; dsimp only at hrun
  have hlook_ud : originalRuntimeCode.lookup (ofString "udivmod") =
      some ([(ofString "a", .one), (ofString "b", .one)],
        sourceFnBody Guest.Software.guestFn_udivmod, .comb [.one, .one]) :=
    lookup_of_guestAst_getElem 33 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_udivmod) rfl
  rcases hl : lookupCodeHOLFinite ent.code.lookup (ofString "udivmod") [.val (.word wlen), .val (.word wsz)] with _ | ⟨fb, fc, fr⟩
  · rw [hl] at hrun; simp at hrun
  · rw [hl] at hrun; dsimp only at hrun
    have hfb := lookupCodeHOLFinite_installed_body ent.code.lookup _ _ _ fb _ fr _ fc (by rw [hcode]; exact hlook_ud) hl
    subst hfb
    have hfr := lookupCodeHOLFinite_installed_return ent _ _ _ _ _ fr _ fc (by rw [hcode]; exact hlook_ud) hl
    subst hfr
    by_cases hz : ent.clock = 0
    · rw [if_pos hz] at hrun; simp at hrun
    · rw [if_neg hz] at hrun
      obtain ⟨wa', wb', heq_vs, hfc_a, hfc_b⟩ :=
        lookupCode_two_words_any_dhi (by decide) hlook_ud (by rwa [hcode] at hl)
      injection heq_vs with h1 h2; injection h1 with h1'; injection h1' with h1''; subst h1''
      injection h2 with h2a _; injection h2a with h2'; injection h2' with h2''; subst h2''
      rcases hud : evaluateHOLFiniteState (callEntryStateHOLFinite ent fc) (sourceFnBody Guest.Software.guestFn_udivmod) with ⟨rud, sud⟩
      rw [hud] at hrun
      cases rud with
      | none => simp at hrun
      | some rud1 =>
        cases rud1 with
        | returned rv_ud =>
          dsimp only at hrun
          obtain ⟨hsz_pos, qw, rw_, rfl, hdiv_eq, _, _⟩ :=
            udivmod_body_returns (callEntryStateHOLFinite ent fc) wlen wsz hcode hfc_a hfc_b rv_ud (by rw [hud])
          have hsh : shapeEqHOL (shapeOfHOLExact (.rStruct [.val (.word qw), .val (.word rw_)] : ValueHOL 64))
              (.comb [.one, .one]) = true := by
            simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL]
          simp only [hsh, Bool.and_self, ↓reduceIte] at hrun
          obtain ⟨_, rSh_ro, _, hlook_ro, hspec_ro⟩ := ro_udivmod
          have hsame_b := Option.some.inj (hlook_ud.symm.trans hlook_ro)
          injection hsame_b with _ hsame_b'; injection hsame_b' with hsame_b'' hsame_r
          subst hsame_b''; subst hsame_r
          have hro := hspec_ro (callEntryStateHOLFinite ent fc) hcode
            (guestInv_callEntry ent fc hG)
            ⟨_, by simpa only [hcode, callEntryStateHOLFinite] using hl⟩
            (by rw [hud]; simp) (by rw [hud]; exact Or.inl ⟨_, rfl⟩)
          rw [hud] at hro; dsimp only at hro
          have hsud_code : sud.code = originalRuntimeCode := by rw [hro]; exact hcode
          let u0 := setVarHOLFinite (ofString "qr") (.rStruct [.val (.word qw), .val (.word rw_)]) { sud with locals := ent.locals }
          have hu0_code : u0.code = originalRuntimeCode := hsud_code
          have hu0_qr : u0.locals.lookup (ofString "qr") = some (.rStruct [.val (.word qw), .val (.word rw_)]) :=
            lookup_setVar_eq _ _ _
          have hu0_lim : u0.locals.lookup (ofString "lim") = some (.val (.word wlim)) := by
            dsimp only [u0]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hlim
          have hret1 : (evaluateHOLFiniteState u0
              (.seq
                (.ite (.cmp .notEqual (.rfield 1 (.var .local (ofString "qr"))) (.const 0#64))
                  (.call (some (none, none)) (ofString "ssz_fail") [.const 30#64]) .skip)
                (.seq
                  (.ite (.cmp .lower (.var .local (ofString "lim")) (.rfield 0 (.var .local (ofString "qr"))))
                    (.call (some (none, none)) (ofString "ssz_fail") [.const 31#64]) .skip)
                  (.return (.rfield 0 (.var .local (ofString "qr"))))))).1 =
              some (.returned rv) := by
            have h1 := congrArg Prod.fst hrun
            simpa using h1
          rw [evaluateHOLFiniteState_seq_line780] at hret1
          rcases hi1 : evaluateHOLFiniteState u0 _ with ⟨ri1, u1⟩
          rw [hi1] at hret1
          cases ri1 with
          | some r1 =>
            exfalso
            have hnr := ite_call0_noret_dhi u0
              (.cmp .notEqual (.rfield 1 (.var .local (ofString "qr"))) (.const 0#64))
              (ofString "ssz_fail") [.const 30#64] rv
            rw [hi1] at hnr; exact hnr hret1
          | none =>
            obtain ⟨hu1_eq, hcond30⟩ := ite_ssz_fail_keeps u0 u1 hu0_code _ _ hi1
            subst hu1_eq
            have hrw0 : rw_.toNat = 0 := by
              simp only [evalHOLExact, evalListHOLExact, toExact, hu0_qr,
                Compiler.Encoders.Asm.wordCmpHOL, valueIsWord, valueWord] at hcond30
              by_cases hr0 : rw_ = 0#64
              · subst hr0; rfl
              · simp [hr0] at hcond30
            dsimp only at hret1
            rw [evaluateHOLFiniteState_seq_line780] at hret1
            rcases hi2 : evaluateHOLFiniteState u0 _ with ⟨ri2, u2⟩
            rw [hi2] at hret1
            cases ri2 with
            | some r2 =>
              exfalso
              have hnr := ite_call0_noret_dhi u0
                (.cmp .lower (.var .local (ofString "lim")) (.rfield 0 (.var .local (ofString "qr"))))
                (ofString "ssz_fail") [.const 31#64] rv
              rw [hi2] at hnr; exact hnr hret1
            | none =>
              obtain ⟨hu2_eq, hcond31⟩ := ite_ssz_fail_keeps u0 u2 hu0_code _ _ hi2
              subst hu2_eq
              have hqw_le : qw.toNat ≤ wlim.toNat := by
                simp only [evalHOLExact, evalListHOLExact, toExact, hu0_lim, hu0_qr,
                  Compiler.Encoders.Asm.wordCmpHOL, valueIsWord, valueWord] at hcond31
                by_cases hlt : wlim < qw
                · simp [hlt] at hcond31
                · exact Nat.le_of_not_lt (fun h => hlt ((BitVec.lt_def).2 h))
              dsimp only at hret1
              rw [evaluateHOLFiniteState_return] at hret1
              simp [evalHOLExact, toExact, hu0_qr, shapeOfHOLExact] at hret1
              exact ⟨hsz_pos, qw, hret1.symm, by omega, hqw_le⟩
        | _ => simp at hrun

theorem while_none_inv_dhi {F : Type}
    (cond : ExpHOL 64) (body : ProgHOL 64)
    (Inv : PanSemStateFiniteExact 64 F → Prop)
    (hdec : ∀ t, Inv t → Inv (decClockHOLFinite t))
    (hno_brk : ∀ t, Inv t → (evaluateHOLFiniteState t body).1 ≠ some .break)
    (hstep : ∀ t (cw : BitVec 64),
      @evalHOLFinite 64 F _ t (fun a => Classical.propDecidable (t.memaddrs a)) cond = some (.val (.word cw)) →
      cw ≠ 0 →
      Inv (decClockHOLFinite t) →
      ((evaluateHOLFiniteState (decClockHOLFinite t) body).1 = none ∨
       (evaluateHOLFiniteState (decClockHOLFinite t) body).1 = some .continue) →
      Inv (evaluateHOLFiniteState (decClockHOLFinite t) body).2) :
    ∀ (k : Nat) (cur : PanSemStateFiniteExact 64 F), cur.clock = k →
      Inv cur →
      (evaluateHOLFiniteState cur (.while cond body)).1 = none →
      Inv (evaluateHOLFiniteState cur (.while cond body)).2 ∧
      (∀ cw : BitVec 64,
        @evalHOLFinite 64 F _ (evaluateHOLFiniteState cur (.while cond body)).2
          (fun a => Classical.propDecidable ((evaluateHOLFiniteState cur (.while cond body)).2.memaddrs a)) cond =
          some (.val (.word cw)) → cw = 0) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro cur hclk hinv hnone
    have hw_eq := evaluateHOLFiniteState_while_fixClockRewrite cur cond body
    rcases hc : @evalHOLFinite 64 F _ cur (fun a => Classical.propDecidable (cur.memaddrs a)) cond with _ | cv
    · rw [hc] at hw_eq; rw [hw_eq] at hnone; simp at hnone
    · rcases cv with ⟨⟨cw⟩⟩ | _ | _
      · rw [hc] at hw_eq; dsimp only at hw_eq
        by_cases hw0 : cw = 0
        · subst hw0; rw [if_neg (by simp)] at hw_eq; rw [hw_eq]
          refine ⟨hinv, fun cw' hcw' => ?_⟩
          change @evalHOLFinite 64 F _ cur (fun a => Classical.propDecidable (cur.memaddrs a)) cond = _ at hcw'
          rw [hc] at hcw'; injection hcw' with h1; injection h1 with h2; injection h2 with h3; exact h3.symm
        · rw [if_pos hw0] at hw_eq
          by_cases hk0 : cur.clock = 0
          · rw [if_pos hk0] at hw_eq; rw [hw_eq] at hnone; simp at hnone
          · rw [if_neg hk0] at hw_eq
            have hinv_d : Inv (decClockHOLFinite cur) := hdec cur hinv
            have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite cur) body
            rcases hbo : evaluateHOLFiniteState (decClockHOLFinite cur) body with ⟨rb, sb⟩
            rw [hbo] at hw_eq hrem
            have hlt : sb.clock < k := by change sb.clock ≤ cur.clock - 1 at hrem; omega
            cases rb with
            | none =>
              dsimp only at hw_eq
              have hinv_sb : Inv sb := by
                have h := hstep cur cw hc hw0 hinv_d (by rw [hbo]; exact Or.inl rfl)
                rwa [hbo] at h
              rw [hw_eq] at hnone ⊢
              exact ih sb.clock hlt sb rfl hinv_sb hnone
            | some r1 =>
              cases r1 with
              | «continue» =>
                dsimp only at hw_eq
                have hinv_sb : Inv sb := by
                  have h := hstep cur cw hc hw0 hinv_d (by rw [hbo]; exact Or.inr rfl)
                  rwa [hbo] at h
                rw [hw_eq] at hnone ⊢
                exact ih sb.clock hlt sb rfl hinv_sb hnone
              | «break» =>
                exfalso
                exact hno_brk (decClockHOLFinite cur) hinv_d (by rw [hbo])
              | _ =>
                dsimp only at hw_eq; rw [hw_eq] at hnone; simp at hnone
      · rw [hc] at hw_eq; rw [hw_eq] at hnone; simp at hnone
      · rw [hc] at hw_eq; rw [hw_eq] at hnone; simp at hnone

theorem ssz_check_offsets_body_returns {F : Type}
    (ent : PanSemStateFiniteExact 64 F) (woffs wn wfixed wlen : BitVec 64)
    (hcode : ent.code = originalRuntimeCode)
    (hoffs : ent.locals.lookup (ofString "offs") = some (.val (.word woffs)))
    (hn : ent.locals.lookup (ofString "n") = some (.val (.word wn)))
    (hfixed : ent.locals.lookup (ofString "fixed") = some (.val (.word wfixed)))
    (hlen : ent.locals.lookup (ofString "len") = some (.val (.word wlen)))
    (hn_pos : 0 < wn.toNat) (hn_lt : wn.toNat < 2 ^ 60)
    (hoffs_hi : woffs.toNat + wn.toNat * 8 ≤ 2 ^ 64)
    (rv : ValueHOL 64) (cpost : PanSemStateFiniteExact 64 F)
    (hrun : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_ssz_check_offsets) =
      (some (.returned rv), cpost)) :
    cpost.memory = ent.memory ∧
    memW ent woffs.toNat = wfixed.toNat ∧
    (∀ j : Nat, j < wn.toNat →
      wfixed.toNat ≤ memW ent (woffs.toNat + j * 8) ∧
      memW ent (woffs.toNat + j * 8) ≤ wlen.toNat) ∧
    (∀ j : Nat, j + 1 < wn.toNat →
      memW ent (woffs.toNat + j * 8) ≤ memW ent (woffs.toNat + (j + 1) * 8)) := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_ssz_check_offsets,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hrun
  rw [evaluateHOLFiniteState_seq_line780] at hrun
  have hwn_ne0 : wn ≠ 0#64 := fun h => by subst h; simp at hn_pos
  have hi0 : evaluateHOLFiniteState ent
      (.ite (.cmp .equal (.var .local (ofString "n")) (.const 0#64)) (.return (.const 0#64)) .skip) =
      (none, ent) := by
    rw [evaluateHOLFiniteState_ite]
    simp [evalHOLExact, evalListHOLExact, toExact, hn, Compiler.Encoders.Asm.wordCmpHOL,
      valueIsWord, valueWord, hwn_ne0, evaluateHOLFiniteState_skip]
  rw [hi0] at hrun; dsimp only at hrun
  rw [evaluateHOLFiniteState_dec_total] at hrun
  simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, ↓reduceIte] at hrun
  let m0 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) ent
  let wcond : ExpHOL 64 := .cmp .less (.var .local (ofString "i")) (.var .local (ofString "n"))
  let wbody : ProgHOL 64 :=
    .dec (ofString "o") .one
      (.load .one (.op .add [.var .local (ofString "offs"), .panop .mul [.var .local (ofString "i"), .const 8#64]]))
      (.seq
        (.ite (.cmp .notEqual (.const 0#64)
            (.op .or [.cmp .lower (.var .local (ofString "o")) (.var .local (ofString "fixed")),
              .cmp .lower (.var .local (ofString "len")) (.var .local (ofString "o"))]))
          (.call (some (none, none)) (ofString "ssz_fail") [.const 10#64]) .skip)
        (.seq
          (.ite (.cmp .less (.const 0#64) (.var .local (ofString "i")))
            (.ite (.cmp .lower (.var .local (ofString "o"))
                (.load .one (.op .sub [.op .add [.var .local (ofString "offs"),
                  .panop .mul [.var .local (ofString "i"), .const 8#64]], .const 8#64])))
              (.call (some (none, none)) (ofString "ssz_fail") [.const 11#64]) .skip)
            .skip)
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64]))))
  let tailP : ProgHOL 64 :=
    .seq
      (.ite (.cmp .notEqual (.load .one (.var .local (ofString "offs"))) (.var .local (ofString "fixed")))
        (.call (some (none, none)) (ofString "ssz_fail") [.const 12#64]) .skip)
      (.return (.const 0#64))
  rcases hseq_w : evaluateHOLFiniteState m0 (.seq (.while wcond wbody) tailP) with ⟨rsw, ssw⟩
  dsimp only [m0, wcond, wbody, tailP] at hseq_w
  rw [hseq_w] at hrun
  injection hrun with hrsw hcpost
  subst hrsw
  have hcpost_mem : cpost.memory = ssw.memory := by rw [← hcpost]
  rw [evaluateHOLFiniteState_seq_line780] at hseq_w
  rcases hw : evaluateHOLFiniteState m0 (.while wcond wbody) with ⟨rw0, sw⟩
  rw [hw] at hseq_w
  have hw_noret : ∀ (t : PanSemStateFiniteExact 64 F), t.code = originalRuntimeCode → ∀ rv', (evaluateHOLFiniteState t (.while wcond wbody)).1 ≠ some (.returned rv') := by
    intro t0 ht0_code rv'
    suffices ∀ k (t : PanSemStateFiniteExact 64 F), t.clock = k → t.code = originalRuntimeCode →
        (evaluateHOLFiniteState t (.while wcond wbody)).1 ≠ some (.returned rv') from
      this t0.clock t0 rfl ht0_code
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro t hk ht_code hret_w
      have hweq := evaluateHOLFiniteState_while_fixClockRewrite t wcond wbody
      rcases hc : @evalHOLFinite 64 F _ t (fun a => Classical.propDecidable (t.memaddrs a)) wcond with _ | cv
      · rw [hc] at hweq; rw [hweq] at hret_w; simp at hret_w
      · rcases cv with ⟨⟨cw⟩⟩ | _ | _
        · rw [hc] at hweq; dsimp only at hweq
          by_cases hw0 : cw = 0
          · subst hw0; rw [if_neg (by simp)] at hweq; rw [hweq] at hret_w; simp at hret_w
          · rw [if_pos hw0] at hweq
            by_cases hk0 : t.clock = 0
            · rw [if_pos hk0] at hweq; rw [hweq] at hret_w; simp at hret_w
            · rw [if_neg hk0] at hweq
              have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite t) wbody
              rcases hb : evaluateHOLFiniteState (decClockHOLFinite t) wbody with ⟨rb, sb⟩
              rw [hb] at hweq hrem
              have hlt : sb.clock < k := by change sb.clock ≤ t.clock - 1 at hrem; omega
              dsimp only [wbody] at hb
              rw [evaluateHOLFiniteState_dec_total] at hb
              dsimp only at hb
              rcases hev_o : @evalHOLExact 64 F _ (decClockHOLFinite t).toExact (fun a => Classical.propDecidable ((decClockHOLFinite t).memaddrs a))
                  (.load .one (.op .add [.var .local (ofString "offs"), .panop .mul [.var .local (ofString "i"), .const 8#64]])) with _ | vo
              · rw [hev_o] at hb; dsimp only at hb; injection hb with hrb _; subst hrb; dsimp only at hweq; rw [hweq] at hret_w; simp at hret_w
              · rw [hev_o] at hb; dsimp only at hb
                by_cases hsho : shapeEqHOL .one (shapeOfHOLExact vo) = true
                · rw [if_pos hsho] at hb
                  let u1 := setVarHOLFinite (ofString "o") vo (decClockHOLFinite t)
                  rw [evaluateHOLFiniteState_seq_line780] at hb
                  rcases hb1 : evaluateHOLFiniteState u1 _ with ⟨rb1, sb1⟩
                  rw [hb1] at hb
                  cases rb1 with
                  | some r1 =>
                    dsimp only at hb
                    injection hb with hrb hsb
                    subst hrb
                    cases r1 with
                    | returned rv'' => exact ite_call0_noret_dhi u1 _ (ofString "ssz_fail") [.const 10#64] rv'' (by rw [hb1])
                    | «continue» => exact absurd (by rw [hb1] : (evaluateHOLFiniteState u1 _).1 = some .continue) (ite_call0_nobreak_dhi u1 _ (ofString "ssz_fail") [.const 10#64]).2
                    | _ => dsimp only at hweq; rw [hweq] at hret_w; simp at hret_w
                  | none =>
                    obtain ⟨hsb1_eq, _⟩ := ite_ssz_fail_keeps u1 sb1 ht_code _ _ hb1
                    subst hsb1_eq
                    dsimp only at hb
                    rw [evaluateHOLFiniteState_seq_line780] at hb
                    rcases hb2 : evaluateHOLFiniteState u1 _ with ⟨rb2, sb2⟩
                    rw [hb2] at hb
                    cases rb2 with
                    | some r2 =>
                      dsimp only at hb
                      injection hb with hrb _
                      subst hrb
                      cases r2 with
                      | returned rv'' => exact (ite2_call0_noctrl_dhi u1 _ _ (ofString "ssz_fail") [.const 11#64]).1 rv'' (by rw [hb2])
                      | «continue» => exact absurd (by rw [hb2] : (evaluateHOLFiniteState u1 _).1 = some .continue) (ite2_call0_noctrl_dhi u1 _ _ (ofString "ssz_fail") [.const 11#64]).2.2
                      | _ => dsimp only at hweq; rw [hweq] at hret_w; simp at hret_w
                    | none =>
                      have hsb2_code_mem : sb2 = u1 := ite2_ssz_fail_none_keeps u1 sb2 ht_code _ _ _ hb2
                      subst hsb2_code_mem
                      dsimp only at hb
                      rw [evaluateHOLFiniteState_assign] at hb
                      rcases hva : @evalHOLExact 64 F _ u1.toExact (fun a => Classical.propDecidable (u1.memaddrs a))
                          (.op .add [.var .local (ofString "i"), .const 1#64]) with _ | va
                      · rw [hva] at hb; dsimp only at hb; injection hb with hrb _; subst hrb; dsimp only at hweq; rw [hweq] at hret_w; simp at hret_w
                      · rw [hva] at hb; dsimp only at hb
                        split at hb
                        · injection hb with hrb hsb
                          subst hrb
                          have hsb_code : sb.code = originalRuntimeCode := by rw [← hsb]; exact ht_code
                          dsimp only at hweq; rw [hweq] at hret_w
                          exact ih sb.clock hlt sb rfl hsb_code hret_w
                        · injection hb with hrb _; subst hrb; dsimp only at hweq; rw [hweq] at hret_w; simp at hret_w
                · rw [if_neg hsho] at hb; injection hb with hrb _; subst hrb; dsimp only at hweq; rw [hweq] at hret_w; simp at hret_w
        · rw [hc] at hweq; rw [hweq] at hret_w; simp at hret_w
        · rw [hc] at hweq; rw [hweq] at hret_w; simp at hret_w
  cases rw0 with
  | some rw1 =>
    exfalso
    dsimp only at hseq_w
    injection hseq_w with hrw1 _
    have hrw1' : rw1 = .returned rv := Option.some.inj hrw1
    subst hrw1'
    exact hw_noret m0 hcode rv (by rw [hw])
  | none =>
    dsimp only at hseq_w
    let Inv : PanSemStateFiniteExact 64 F → Prop := fun t =>
      t.code = originalRuntimeCode ∧
      t.memory = ent.memory ∧
      t.memaddrs = ent.memaddrs ∧
      t.locals.lookup (ofString "offs") = some (.val (.word woffs)) ∧
      t.locals.lookup (ofString "n") = some (.val (.word wn)) ∧
      t.locals.lookup (ofString "fixed") = some (.val (.word wfixed)) ∧
      t.locals.lookup (ofString "len") = some (.val (.word wlen)) ∧
      ∃ wi : BitVec 64,
        t.locals.lookup (ofString "i") = some (.val (.word wi)) ∧
        wi.toNat ≤ wn.toNat ∧
        (∀ j < wi.toNat,
          wfixed.toNat ≤ memW ent (woffs.toNat + j * 8) ∧
          memW ent (woffs.toNat + j * 8) ≤ wlen.toNat) ∧
        (∀ j, j + 1 < wi.toNat →
          memW ent (woffs.toNat + j * 8) ≤ memW ent (woffs.toNat + (j + 1) * 8))
    have hInv0 : Inv m0 := by
      refine ⟨hcode, rfl, rfl, ?_, ?_, ?_, ?_, 0#64, lookup_setVar_eq _ _ _, by simp,
        fun j hj => by simp at hj, fun j hj => by simp at hj⟩ <;>
        (dsimp only [m0]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; assumption)
    have hno_brk : ∀ t, Inv t → (evaluateHOLFiniteState t wbody).1 ≠ some .break := by
      intro t ht hbrk
      dsimp only [wbody] at hbrk
      rw [evaluateHOLFiniteState_dec_total] at hbrk
      dsimp only at hbrk
      rcases hev_o : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
          (.load .one (.op .add [.var .local (ofString "offs"), .panop .mul [.var .local (ofString "i"), .const 8#64]])) with _ | vo
      · rw [hev_o] at hbrk; simp at hbrk
      · rw [hev_o] at hbrk; dsimp only at hbrk
        by_cases hsho : shapeEqHOL .one (shapeOfHOLExact vo) = true
        · rw [if_pos hsho] at hbrk
          let u1 := setVarHOLFinite (ofString "o") vo t
          rw [evaluateHOLFiniteState_seq_line780] at hbrk
          rcases hb1 : evaluateHOLFiniteState u1 _ with ⟨rb1, sb1⟩
          rw [hb1] at hbrk
          cases rb1 with
          | some r1 =>
            dsimp only at hbrk
            have h1 : r1 = .break := Option.some.inj hbrk
            subst h1
            exact (ite_call0_nobreak_dhi u1 _ (ofString "ssz_fail") [.const 10#64]).1 (by rw [hb1])
          | none =>
            obtain ⟨hsb1, _⟩ := ite_ssz_fail_keeps u1 sb1 ht.1 _ _ hb1
            subst hsb1; dsimp only at hbrk
            rw [evaluateHOLFiniteState_seq_line780] at hbrk
            rcases hb2 : evaluateHOLFiniteState u1 _ with ⟨rb2, sb2⟩
            rw [hb2] at hbrk
            cases rb2 with
            | some r2 =>
              dsimp only at hbrk
              have h2 : r2 = .break := Option.some.inj hbrk
              subst h2
              exact (ite2_call0_noctrl_dhi u1 _ _ (ofString "ssz_fail") [.const 11#64]).2.1 (by rw [hb2])
            | none =>
              dsimp only at hbrk
              rw [evaluateHOLFiniteState_assign] at hbrk
              rcases hva : @evalHOLExact 64 F _ sb2.toExact (fun a => Classical.propDecidable (sb2.memaddrs a))
                  (.op .add [.var .local (ofString "i"), .const 1#64]) with _ | va
              · rw [hva] at hbrk; simp at hbrk
              · rw [hva] at hbrk; dsimp only at hbrk; split at hbrk <;> simp at hbrk
        · rw [if_neg hsho] at hbrk; simp at hbrk
    have hstep_w : ∀ t (cw : BitVec 64),
        @evalHOLFinite 64 F _ t (fun a => Classical.propDecidable (t.memaddrs a)) wcond = some (.val (.word cw)) →
        cw ≠ 0 →
        Inv (decClockHOLFinite t) →
        ((evaluateHOLFiniteState (decClockHOLFinite t) wbody).1 = none ∨
         (evaluateHOLFiniteState (decClockHOLFinite t) wbody).1 = some .continue) →
        Inv (evaluateHOLFiniteState (decClockHOLFinite t) wbody).2 := by
      intro t cw hcond hnz ⟨ht_code, ht_mem, ht_dom, ht_offs, ht_n, ht_fixed, ht_len, wi, ht_i, hwi_le, hbounds, hmono⟩ hnc
      have hloc_offs : t.locals.lookup (ofString "offs") = some (.val (.word woffs)) := ht_offs
      have hloc_n : t.locals.lookup (ofString "n") = some (.val (.word wn)) := ht_n
      have hloc_fixed : t.locals.lookup (ofString "fixed") = some (.val (.word wfixed)) := ht_fixed
      have hloc_len : t.locals.lookup (ofString "len") = some (.val (.word wlen)) := ht_len
      have hloc_i : t.locals.lookup (ofString "i") = some (.val (.word wi)) := ht_i
      have hmem_t : t.memory = ent.memory := ht_mem
      have hdom_t : t.memaddrs = ent.memaddrs := ht_dom
      have hcode_t : t.code = originalRuntimeCode := ht_code
      have hwi_lt : wi.toNat < wn.toNat := by
        rw [evalHOLFinite_eq_toExact] at hcond
        simp only [wcond, evalHOLExact, evalListHOLExact, toExact, hloc_i, hloc_n,
          Compiler.Encoders.Asm.wordCmpHOL,
          holAsmSignedLess_small wi wn (by omega) (by omega)] at hcond
        by_cases hlt : wi.toNat < wn.toNat
        · exact hlt
        · simp [hlt] at hcond; exact absurd hcond.symm hnz
      rcases hbo_ev : evaluateHOLFiniteState (decClockHOLFinite t) wbody with ⟨rb_step, sb_step⟩
      have hnc' : rb_step = none ∨ rb_step = some .continue := by
        rcases hnc with h | h
        · exact Or.inl (by rw [← h, hbo_ev])
        · exact Or.inr (by rw [← h, hbo_ev])
      show Inv sb_step
      dsimp only [wbody] at hbo_ev
      rw [evaluateHOLFiniteState_dec_total] at hbo_ev
      dsimp only at hbo_ev
      rcases hev_o : @evalHOLExact 64 F _ (decClockHOLFinite t).toExact (fun a => Classical.propDecidable ((decClockHOLFinite t).memaddrs a))
          (.load .one (.op .add [.var .local (ofString "offs"), .panop .mul [.var .local (ofString "i"), .const 8#64]])) with _ | vo
      · rw [hev_o] at hbo_ev; dsimp only at hbo_ev
        injection hbo_ev with hrb_eq _
        rw [← hrb_eq] at hnc'
        rcases hnc' with h | h <;> cases h
      · rw [hev_o] at hbo_ev; dsimp only at hbo_ev
        by_cases hsho : shapeEqHOL .one (shapeOfHOLExact vo) = true
        · rw [if_pos hsho] at hbo_ev
          obtain ⟨wo, rfl⟩ := eval_load_one_word (decClockHOLFinite t) _ vo hev_o
          have hmul_eq : (wi * 8#64).toNat = wi.toNat * 8 := by
            rw [BitVec.toNat_mul, show (8#64 : BitVec 64).toNat = 8 from rfl, Nat.mod_eq_of_lt (by omega)]
          have haddr_eq : (woffs + wi * 8#64).toNat = woffs.toNat + wi.toNat * 8 := by
            rw [BitVec.toNat_add_of_lt] <;> omega
          have hwo_eq : wo.toNat = memW ent (woffs.toNat + wi.toNat * 8) := by
            change @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
              (.load .one (.op .add [.var .local (ofString "offs"), .panop .mul [.var .local (ofString "i"), .const 8#64]])) =
              some (.val (.word wo)) at hev_o
            have hadd_ev : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
                (.op .add [.var .local (ofString "offs"), .panop .mul [.var .local (ofString "i"), .const 8#64]]) =
                some (.val (.word (woffs + wi * 8#64))) := by
              simp [evalHOLExact, panOpHOL, evalListHOLExact, toExact, hloc_offs, hloc_i,
                wordOpHOL, wordOp, valueIsWord, valueWord]
            unfold evalHOLExact at hev_o
            rw [hadd_ev] at hev_o
            by_cases hdom_a : t.memaddrs (woffs + wi * 8#64)
            · rcases hwlab : ent.memory (woffs + wi * 8#64) with ⟨w_loaded⟩
              simp [isWfShapeExactHOL, memLoadHOLExact, panMemLoadHOL, toExact, hmem_t, hdom_a, hwlab] at hev_o
              subst hev_o
              have hbv : BitVec.ofNat 64 (woffs.toNat + wi.toNat * 8) = woffs + wi * 8#64 := by
                apply BitVec.eq_of_toNat_eq
                rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), haddr_eq]
              simp [memW, hbv, hwlab]
            · simp [isWfShapeExactHOL, memLoadHOLExact, panMemLoadHOL, toExact, hdom_a] at hev_o
          let u1 := setVarHOLFinite (ofString "o") (.val (.word wo)) (decClockHOLFinite t)
          have hu1_o : u1.locals.lookup (ofString "o") = some (.val (.word wo)) := lookup_setVar_eq _ _ _
          have hu1_offs : u1.locals.lookup (ofString "offs") = some (.val (.word woffs)) := by
            dsimp only [u1]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hloc_offs
          have hu1_n : u1.locals.lookup (ofString "n") = some (.val (.word wn)) := by
            dsimp only [u1]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hloc_n
          have hu1_fixed : u1.locals.lookup (ofString "fixed") = some (.val (.word wfixed)) := by
            dsimp only [u1]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hloc_fixed
          have hu1_len : u1.locals.lookup (ofString "len") = some (.val (.word wlen)) := by
            dsimp only [u1]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hloc_len
          have hu1_i : u1.locals.lookup (ofString "i") = some (.val (.word wi)) := by
            dsimp only [u1]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hloc_i
          have hu1_mem : u1.memory = ent.memory := hmem_t
          have hu1_dom : u1.memaddrs = ent.memaddrs := hdom_t
          have hu1_code : u1.code = originalRuntimeCode := hcode_t
          rw [evaluateHOLFiniteState_seq_line780] at hbo_ev
          rcases hb1 : evaluateHOLFiniteState u1 _ with ⟨rb1, sb1⟩
          rw [hb1] at hbo_ev
          cases rb1 with
          | some r1 =>
            exfalso
            dsimp only at hbo_ev
            injection hbo_ev with hrb_eq _
            rw [← hrb_eq] at hnc'
            rcases hnc' with h1 | h1
            · cases h1
            · injection h1 with h1'; subst h1'
              exact (ite_call0_nobreak_dhi u1 _ (ofString "ssz_fail") [.const 10#64]).2 (by rw [hb1])
          | none =>
            obtain ⟨hsb1_eq, hcond10⟩ := ite_ssz_fail_keeps u1 sb1 hu1_code _ _ hb1
            subst hsb1_eq
            have hwo_bounds : wfixed.toNat ≤ wo.toNat ∧ wo.toNat ≤ wlen.toNat := by
              simp only [evalHOLExact, evalListHOLExact, toExact, hu1_o, hu1_fixed, hu1_len,
                wordOpHOL, wordOp, Compiler.Encoders.Asm.wordCmpHOL, valueIsWord, valueWord] at hcond10
              constructor
              · by_cases h1 : wo < wfixed
                · exfalso
                  by_cases h2 : wlen < wo <;>
                    (simp [h1, h2, valueIsWord, valueWord] at hcond10; revert hcond10; decide)
                · exact Nat.le_of_not_lt (fun h => h1 ((BitVec.lt_def).2 h))
              · by_cases h2 : wlen < wo
                · exfalso
                  by_cases h1 : wo < wfixed <;>
                    (simp [h1, h2, valueIsWord, valueWord] at hcond10; revert hcond10; decide)
                · exact Nat.le_of_not_lt (fun h => h2 ((BitVec.lt_def).2 h))
            dsimp only at hbo_ev
            rw [evaluateHOLFiniteState_seq_line780] at hbo_ev
            rcases hb2 : evaluateHOLFiniteState u1 _ with ⟨rb2, sb2⟩
            rw [hb2] at hbo_ev
            cases rb2 with
            | some r2 =>
              exfalso
              dsimp only at hbo_ev
              injection hbo_ev with hrb_eq _
              rw [← hrb_eq] at hnc'
              rcases hnc' with h2 | h2
              · cases h2
              · injection h2 with h2'; subst h2'
                exact (ite2_call0_noctrl_dhi u1 _ _ (ofString "ssz_fail") [.const 11#64]).2.2 (by rw [hb2])
            | none =>
              obtain ⟨hsb2_eq, hprev_le⟩ : sb2 = u1 ∧ (0 < wi.toNat → memW ent (woffs.toNat + (wi.toNat - 1) * 8) ≤ wo.toNat) := by
                rw [evaluateHOLFiniteState_ite] at hb2
                have hcond_i : @evalHOLExact 64 F _ u1.toExact (fun a => Classical.propDecidable (u1.memaddrs a))
                    (.cmp .less (.const 0#64) (.var .local (ofString "i"))) =
                    some (.val (.word (if 0 < wi.toNat then 1#64 else 0#64))) := by
                  simp only [evalHOLExact, evalListHOLExact, toExact, hu1_i,
                    Compiler.Encoders.Asm.wordCmpHOL,
                    holAsmSignedLess_small 0#64 wi (by decide) (by omega), valueIsWord, valueWord]
                  by_cases hpos : 0 < wi.toNat <;> simp [hpos]
                rw [hcond_i] at hb2; dsimp only at hb2
                by_cases hpos : 0 < wi.toNat
                · simp only [hpos, ↓reduceIte] at hb2
                  rw [if_neg (by decide : (1#64 : BitVec 64) ≠ 0)] at hb2
                  obtain ⟨hsb2_eq, hcond11⟩ := ite_ssz_fail_keeps u1 sb2 hu1_code
                    (.cmp .lower (.var .local (ofString "o"))
                      (.load .one (.op .sub [.op .add [.var .local (ofString "offs"),
                        .panop .mul [.var .local (ofString "i"), .const 8#64]], .const 8#64])))
                    (.const 11#64) hb2
                  refine ⟨hsb2_eq, fun _ => ?_⟩
                  have hsub_ev : @evalHOLExact 64 F _ u1.toExact (fun a => Classical.propDecidable (u1.memaddrs a))
                      (.op .sub [.op .add [.var .local (ofString "offs"),
                        .panop .mul [.var .local (ofString "i"), .const 8#64]], .const 8#64]) =
                      some (.val (.word (woffs + wi * 8#64 - 8#64))) := by
                    simp [evalHOLExact, panOpHOL, evalListHOLExact, toExact, hu1_offs, hu1_i,
                      wordOpHOL, wordOp, valueIsWord, valueWord]
                  have hsub_eq : (woffs + wi * 8#64 - 8#64).toNat = woffs.toNat + (wi.toNat - 1) * 8 := by
                    have h1 : 8 ≤ (woffs + wi * 8#64).toNat := by omega
                    rw [BitVec.toNat_sub_of_le (by exact (BitVec.le_def).2 h1)]
                    have h8 : (8#64 : BitVec 64).toNat = 8 := rfl
                    omega
                  have ho_ev : @evalHOLExact 64 F _ u1.toExact (fun a => Classical.propDecidable (u1.memaddrs a))
                      (.var .local (ofString "o")) = some (.val (.word wo)) := by
                    simp [evalHOLExact, toExact, hu1_o]
                  unfold evalHOLExact at hcond11
                  rw [ho_ev] at hcond11
                  unfold evalHOLExact at hcond11
                  rw [hsub_ev] at hcond11
                  by_cases hdom_p : u1.memaddrs (woffs + wi * 8#64 - 8#64)
                  · rcases hwlab_p : ent.memory (woffs + wi * 8#64 - 8#64) with ⟨wp_loaded⟩
                    simp [isWfShapeExactHOL, memLoadHOLExact, panMemLoadHOL, toExact, hu1_mem, hdom_p, hwlab_p] at hcond11
                    have hbv_p : BitVec.ofNat 64 (woffs.toNat + (wi.toNat - 1) * 8) = woffs + wi * 8#64 - 8#64 := by
                      apply BitVec.eq_of_toNat_eq
                      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hsub_eq]
                    have hwp_eq : memW ent (woffs.toNat + (wi.toNat - 1) * 8) = wp_loaded.toNat := by
                      simp [memW, hbv_p, hwlab_p]
                    rw [hwp_eq]
                    by_cases hlt_p : wo < wp_loaded
                    · simp [Compiler.Encoders.Asm.wordCmpHOL, hlt_p] at hcond11
                    · exact Nat.le_of_not_lt (fun h => hlt_p ((BitVec.lt_def).2 h))
                  · simp [isWfShapeExactHOL, memLoadHOLExact, panMemLoadHOL, toExact, hdom_p] at hcond11
                · simp only [hpos, ↓reduceIte] at hb2
                  rw [if_pos (by decide : (0#64 : BitVec 64) = 0), evaluateHOLFiniteState_skip] at hb2
                  injection hb2 with _ h; exact ⟨h.symm, fun hp => absurd hp hpos⟩
              subst hsb2_eq
              dsimp only at hbo_ev
              rw [evaluateHOLFiniteState_assign] at hbo_ev
              have hev_inc : @evalHOLExact 64 F _ u1.toExact (fun a => Classical.propDecidable (u1.memaddrs a))
                  (.op .add [.var .local (ofString "i"), .const 1#64]) = some (.val (.word (wi + 1#64))) := by
                simp [evalHOLExact, evalListHOLExact, toExact, hu1_i, wordOpHOL, wordOp, valueIsWord, valueWord]
              have hvv_i : u1.isValidValueHOLFinite .local (ofString "i") (.val (.word (wi + 1#64))) = true := by
                simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, toExact, hu1_i,
                  shapeOfHOLExact, shapeEqHOL]
              simp only [hev_inc, hvv_i, ↓reduceIte, setKvarHOLFinite] at hbo_ev
              injection hbo_ev with _ hsb_step_eq
              rw [← hsb_step_eq]
              have hwi1_nat : (wi + 1#64).toNat = wi.toNat + 1 := by
                rw [BitVec.toNat_add_of_lt]
                · rfl
                · change wi.toNat + 1 < 2 ^ 64; omega
              refine ⟨hu1_code, hu1_mem, hu1_dom, ?_, ?_, ?_, ?_, wi + 1#64, ?_, by omega, ?_, ?_⟩
              · simp only [PanRunBounded.resVarEq_lookup, show ofString "offs" ≠ ofString "o" by decide, ↓reduceIte]
                rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hu1_offs
              · simp only [PanRunBounded.resVarEq_lookup, show ofString "n" ≠ ofString "o" by decide, ↓reduceIte]
                rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hu1_n
              · simp only [PanRunBounded.resVarEq_lookup, show ofString "fixed" ≠ ofString "o" by decide, ↓reduceIte]
                rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hu1_fixed
              · simp only [PanRunBounded.resVarEq_lookup, show ofString "len" ≠ ofString "o" by decide, ↓reduceIte]
                rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hu1_len
              · simp only [PanRunBounded.resVarEq_lookup, show ofString "i" ≠ ofString "o" by decide, ↓reduceIte]
                exact lookup_setVar_eq _ _ _
              · intro j hj
                rw [hwi1_nat] at hj
                by_cases hjeq : j = wi.toNat
                · subst hjeq; rw [← hwo_eq]; exact hwo_bounds
                · exact hbounds j (by omega)
              · intro j hj
                rw [hwi1_nat] at hj
                by_cases hjeq : j + 1 = wi.toNat
                · have hj_sub : j = wi.toNat - 1 := by omega
                  have hpos : 0 < wi.toNat := by omega
                  have hp := hprev_le hpos
                  rw [← hj_sub, hwo_eq] at hp
                  rwa [hjeq]
                · exact hmono j (by omega)
        · rw [if_neg hsho] at hbo_ev
          injection hbo_ev with hrb_eq _
          rw [← hrb_eq] at hnc'
          rcases hnc' with h | h <;> cases h
    obtain ⟨hInv_sw, hcond_exit⟩ := while_none_inv_dhi wcond wbody Inv
      (fun t ht => ht) hno_brk hstep_w
      m0.clock m0 rfl hInv0 (by rw [hw])
    rw [hw] at hInv_sw hcond_exit
    obtain ⟨hsw_code, hsw_mem, hsw_dom, hsw_offs, hsw_n, hsw_fixed, hsw_len, wi_end, hsw_i, hwi_end_le, hbounds_end, hmono_end⟩ := hInv_sw
    have hwi_end_eq : wi_end.toNat = wn.toNat := by
      have hev_end : @evalHOLFinite 64 F _ sw (fun a => Classical.propDecidable (sw.memaddrs a)) wcond =
          some (.val (.word (if wi_end.toNat < wn.toNat then 1#64 else 0#64))) := by
        rw [evalHOLFinite_eq_toExact]
        have hi_sw : sw.locals.lookup (ofString "i") = some (.val (.word wi_end)) := hsw_i
        have hn_sw : sw.locals.lookup (ofString "n") = some (.val (.word wn)) := hsw_n
        simp [wcond, evalHOLExact, evalListHOLExact, toExact, hi_sw, hn_sw,
          Compiler.Encoders.Asm.wordCmpHOL,
          holAsmSignedLess_small wi_end wn (by omega) (by omega)]
      have h0 := hcond_exit _ hev_end
      by_cases hlt : wi_end.toNat < wn.toNat
      · simp [hlt] at h0
      · omega
    rw [evaluateHOLFiniteState_seq_line780] at hseq_w
    rcases hit12 : evaluateHOLFiniteState sw _ with ⟨rit12, sit12⟩
    rw [hit12] at hseq_w
    cases rit12 with
    | some r12 =>
      exfalso
      dsimp only at hseq_w
      injection hseq_w with hr12 _
      have hr12' : r12 = .returned rv := Option.some.inj hr12
      subst hr12'
      exact ite_call0_noret_dhi sw _ (ofString "ssz_fail") [.const 12#64] rv (by rw [hit12])
    | none =>
      dsimp only at hseq_w
      obtain ⟨hsit12_eq, hcond12⟩ := ite_ssz_fail_keeps sw sit12 hsw_code _ _ hit12
      rw [hsit12_eq] at hseq_w
      rw [evaluateHOLFiniteState_return] at hseq_w
      simp [evalHOLExact, shapeOfHOLExact] at hseq_w
      obtain ⟨_, hssw_eq⟩ := hseq_w
      have hcpost_mem' : cpost.memory = sw.memory := by
        rw [hcpost_mem, ← hssw_eq]
        rfl
      have hoffs_sw : sw.locals.lookup (ofString "offs") = some (.val (.word woffs)) := hsw_offs
      have hfixed_sw : sw.locals.lookup (ofString "fixed") = some (.val (.word wfixed)) := hsw_fixed
      have hmem_sw : sw.memory = ent.memory := hsw_mem
      have hdom_sw : sw.memaddrs = ent.memaddrs := hsw_dom
      have hmem0_eq : memW ent woffs.toNat = wfixed.toNat := by
        change @evalHOLExact 64 F _ sw.toExact (fun a => Classical.propDecidable (sw.memaddrs a))
          (ExpHOL.cmp Cmp.notEqual (ExpHOL.load ShapeHOL.one (ExpHOL.var VarKind.local (ofString "offs")))
            (ExpHOL.var VarKind.local (ofString "fixed"))) =
          some (.val (.word 0#64)) at hcond12
        by_cases hdom0 : sw.memaddrs woffs
        · rcases hwlab0 : ent.memory woffs with ⟨w0_loaded⟩
          simp [evalHOLExact, evalListHOLExact, toExact, hoffs_sw, hfixed_sw, hmem_sw,
            isWfShapeExactHOL, memLoadHOLExact, panMemLoadHOL, hdom0, hwlab0,
            valueIsWord, valueWord] at hcond12
          have hbv0 : BitVec.ofNat 64 woffs.toNat = woffs := by
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt woffs.isLt]
          simp only [memW, hbv0, hwlab0]
          by_cases heq0 : w0_loaded = wfixed
          · subst heq0; rfl
          · simp [Compiler.Encoders.Asm.wordCmpHOL, heq0] at hcond12
        · simp [evalHOLExact, evalListHOLExact, toExact, hoffs_sw, hfixed_sw,
            isWfShapeExactHOL, memLoadHOLExact, panMemLoadHOL, hdom0] at hcond12
      rw [hwi_end_eq] at hbounds_end hmono_end
      exact ⟨hcpost_mem'.trans hmem_sw, hmem0_eq, hbounds_end, hmono_end⟩


end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
