import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkDhiSszChecks
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

/-! ### Stepping / Return Unpacking Combinators -/

theorem seq_returned_split {F : Type}
    {cur post : PanSemStateFiniteExact 64 F} {a b : ProgHOL 64} {rv : ValueHOL 64}
    (ha_noret : ∀ rv', (evaluateHOLFiniteState cur a).1 ≠ some (.returned rv'))
    (hrun : evaluateHOLFiniteState cur (.seq a b) = (some (.returned rv), post)) :
    ∃ mid,
      evaluateHOLFiniteState cur a = (none, mid) ∧
      evaluateHOLFiniteState mid b = (some (.returned rv), post) := by
  rw [evaluateHOLFiniteState_seq_line780] at hrun
  rcases ha : evaluateHOLFiniteState cur a with ⟨ra, mid⟩
  rw [ha] at hrun
  cases ra with
  | none => exact ⟨mid, rfl, hrun⟩
  | some r1 =>
    dsimp only at hrun
    injection hrun with hr1 _
    have hr1' : r1 = .returned rv := Option.some.inj hr1
    subst hr1'
    exact absurd ha (by intro _; exact ha_noret rv (by rw [ha]))

theorem dec_returned_split {F : Type}
    {cur post : PanSemStateFiniteExact 64 F} {nm : MlS} {sh : ShapeHOL}
    {rhs : ExpHOL 64} {body : ProgHOL 64} {rv : ValueHOL 64}
    (hrun : evaluateHOLFiniteState cur (.dec nm sh rhs body) = (some (.returned rv), post)) :
    ∃ v post0,
      @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) rhs = some v ∧
      shapeEqHOL sh (shapeOfHOLExact v) = true ∧
      evaluateHOLFiniteState (setVarHOLFinite nm v cur) body = (some (.returned rv), post0) ∧
      post = { post0 with locals := HolFiniteMapExact.resVarEq post0.locals (nm, cur.locals.lookup nm) } := by
  rw [evaluateHOLFiniteState_dec_total] at hrun
  dsimp only at hrun
  rcases hv : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) rhs with _ | v
  · rw [hv] at hrun; simp at hrun
  · rw [hv] at hrun; dsimp only at hrun
    by_cases hsh : shapeEqHOL sh (shapeOfHOLExact v) = true
    · rw [if_pos hsh] at hrun
      rcases hb : evaluateHOLFiniteState (setVarHOLFinite nm v cur) body with ⟨rb, post0⟩
      rw [hb] at hrun; dsimp only at hrun
      injection hrun with hrb hpost
      subst hrb
      exact ⟨v, post0, rfl, hsh, hb, hpost.symm⟩
    · rw [if_neg hsh] at hrun; simp at hrun

theorem dec_cont_or_none_split {F : Type}
    {cur : PanSemStateFiniteExact 64 F} {nm : MlS} {sh : ShapeHOL}
    {rhs : ExpHOL 64} {body : ProgHOL 64}
    (hf : (evaluateHOLFiniteState cur (.dec nm sh rhs body)).1 = none ∨
          (evaluateHOLFiniteState cur (.dec nm sh rhs body)).1 = some .continue) :
    ∃ v,
      @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) rhs = some v ∧
      shapeEqHOL sh (shapeOfHOLExact v) = true ∧
      ((evaluateHOLFiniteState (setVarHOLFinite nm v cur) body).1 = none ∨
       (evaluateHOLFiniteState (setVarHOLFinite nm v cur) body).1 = some .continue) ∧
      (evaluateHOLFiniteState cur (.dec nm sh rhs body)).2 =
        { (evaluateHOLFiniteState (setVarHOLFinite nm v cur) body).2 with
          locals := HolFiniteMapExact.resVarEq
            (evaluateHOLFiniteState (setVarHOLFinite nm v cur) body).2.locals (nm, cur.locals.lookup nm) } := by
  have hrun := evaluateHOLFiniteState_dec_total cur nm sh rhs body
  rcases h0 : evaluateHOLFiniteState cur (.dec nm sh rhs body) with ⟨r, post⟩
  rw [h0] at hf hrun
  dsimp only at hf hrun ⊢
  rcases hv : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) rhs with _ | v
  · rw [hv] at hrun; injection hrun with hr _; subst hr; rcases hf with h | h <;> simp at h
  · rw [hv] at hrun; dsimp only at hrun
    by_cases hsh : shapeEqHOL sh (shapeOfHOLExact v) = true
    · rw [if_pos hsh] at hrun
      injection hrun with hr hpost
      subst hpost
      exact ⟨v, rfl, hsh, hr.symm ▸ hf, rfl⟩
    · rw [if_neg hsh] at hrun; injection hrun with hr _; subst hr; rcases hf with h | h <;> simp at h

theorem decCall_returned_split {F : Type}
    {cur post : PanSemStateFiniteExact 64 F} {nm : MlS} {sh : ShapeHOL}
    {fn : MlS} {args : List (ExpHOL 64)} {cont : ProgHOL 64} {rv : ValueHOL 64}
    {params : List (MlS × ShapeHOL)} {fbody : ProgHOL 64} {rsh : ShapeHOL}
    (hcode : cur.code = originalRuntimeCode)
    (hlook : originalRuntimeCode.lookup fn = some (params, fbody, rsh))
    (hrun : evaluateHOLFiniteState cur (.decCall nm sh fn args cont) = (some (.returned rv), post)) :
    ∃ vals callee crv cpost post0,
      evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) args = some vals ∧
      lookupCodeHOLFinite originalRuntimeCode.lookup fn vals = some (fbody, callee, rsh) ∧
      cur.clock ≠ 0 ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite cur callee) fbody = (some (.returned crv), cpost) ∧
      shapeEqHOL (shapeOfHOLExact crv) sh = true ∧
      shapeEqHOL (shapeOfHOLExact crv) rsh = true ∧
      evaluateHOLFiniteState (setVarHOLFinite nm crv { cpost with locals := cur.locals }) cont =
        (some (.returned rv), post0) ∧
      post = { post0 with locals := HolFiniteMapExact.resVarEq post0.locals (nm, cur.locals.lookup nm) } := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hrun
  rcases hargs : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) args with _ | vals
  · rw [hargs] at hrun; simp at hrun
  · rw [hargs] at hrun; dsimp only at hrun
    rcases hl : lookupCodeHOLFinite cur.code.lookup fn vals with _ | ⟨fb, fc, fr⟩
    · rw [hl] at hrun; simp at hrun
    · rw [hl] at hrun; dsimp only at hrun
      have hfb := lookupCodeHOLFinite_installed_body cur.code.lookup fn _ _ fb _ fr vals fc (by rw [hcode]; exact hlook) hl
      have hfr := lookupCodeHOLFinite_installed_return cur fn _ _ _ _ fr vals fc (by rw [hcode]; exact hlook) hl
      rw [hfb, hfr] at hl hrun
      by_cases hz : cur.clock = 0
      · rw [if_pos hz] at hrun; simp at hrun
      · rw [if_neg hz] at hrun
        rcases hc : evaluateHOLFiniteState (callEntryStateHOLFinite cur fc) fbody with ⟨rc, cpost⟩
        rw [hc] at hrun
        cases rc with
        | none => simp at hrun
        | some r1 =>
          cases r1 with
          | returned crv =>
            dsimp only at hrun
            by_cases hsh : (shapeEqHOL (shapeOfHOLExact crv) sh && shapeEqHOL (shapeOfHOLExact crv) rsh) = true
            · rw [if_pos hsh] at hrun
              obtain ⟨hsh1, hsh2⟩ := Bool.and_eq_true _ _ ▸ hsh
              rcases hk : evaluateHOLFiniteState (setVarHOLFinite nm crv { cpost with locals := cur.locals }) cont with ⟨rk, post0⟩
              rw [hk] at hrun; dsimp only at hrun
              injection hrun with hrk hpost
              subst hrk
              exact ⟨vals, fc, crv, cpost, post0, rfl, by rwa [← hcode], hz, hc, hsh1, hsh2, hk, hpost.symm⟩
            · rw [if_neg hsh] at hrun; simp at hrun
          | _ => simp at hrun

theorem decCall_alloc_returned_split {F : Type}
    {s cur post : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {B : List (String × Nat)}
    {nm : MlS} {szExp : ExpHOL 64} {cont : ProgHOL 64} {rv : ValueHOL 64}
    (heff : WorldEff s cur Rl B dhiGw)
    (hrun : evaluateHOLFiniteState cur (.decCall nm .one (ofString "alloc") [szExp] cont) = (some (.returned rv), post)) :
    ∃ (pw nw : BitVec 64) (mid post0 : PanSemStateFiniteExact 64 F),
      @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) szExp = some (.val (.word nw)) ∧
      mid.memory = cur.memory ∧
      mid.locals = cur.locals.update (nm, .val (.word pw)) ∧
      (∀ k : MlS, k ≠ ofString "heap_ptr" → mid.globals.lookup k = cur.globals.lookup k) ∧
      WorldEff s mid Rl B dhiGw ∧
      pw.toNat % 8 = 0 ∧
      sourceBase ≤ pw.toNat ∧
      globN s "heap_ptr" ≤ pw.toNat ∧
      pw.toNat + (nw.toNat + 7) / 8 * 8 = globN mid "heap_ptr" ∧
      globN mid "heap_ptr" ≤ heapLimit ∧
      WordsOK mid (pw.toNat, (nw.toNat + 7) / 8 * 8) ∧
      evaluateHOLFiniteState mid cont = (some (.returned rv), post0) ∧
      post = { post0 with locals := HolFiniteMapExact.resVarEq post0.locals (nm, cur.locals.lookup nm) } := by
  obtain ⟨vals, fc, crv, pa, post0, hargs, hl, _, hc, _, _, hk, hpost⟩ :=
    decCall_returned_split heff.code lookup_alloc hrun
  obtain ⟨nw, rfl, hnw_fc⟩ := lookupCode_one_word lookup_alloc hl
  have hsz_ev : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) szExp =
      some (.val (.word nw)) := by
    rw [evalListHOLFinite_eq_toExact] at hargs
    simp only [evalListHOLExact] at hargs
    split at hargs <;> simp at hargs
    rename_i v hv _; rw [hargs.1] at hv; exact hv
  obtain ⟨pw, hpw_lk⟩ : ∃ pw : BitVec 64, cur.globals.lookup (ofString "heap_ptr") = some (.val (.word pw)) :=
    globalWord_of_globN_pos cur "heap_ptr" (by have := heff.arena.2.1; rw [sourceBase_val] at this; omega)
  let entry := callEntryStateHOLFinite cur fc
  have hal := InitECandidate.Solver.Wave8GuestInv.R13.alloc_body_resumes entry pw heff.code hpw_lk
    (by dsimp only [entry]; rw [hc]; exact Or.inl ⟨crv, rfl⟩)
  dsimp only [entry] at hal
  rw [hc] at hal
  obtain ⟨nw', hnw'_lk, hrv_eq, hcmp1, hcmp2, hpa_eq⟩ := hal
  have hnw_eq : nw = nw' := by
    have : (callEntryStateHOLFinite cur fc).locals.lookup (ofString "n") = some (.val (.word nw)) := hnw_fc
    rw [this] at hnw'_lk; injection hnw'_lk with h'; injection h' with h'; injection h'
  subst hnw_eq
  dsimp only at hrv_eq hpa_eq
  injection hrv_eq with hrv_eq'; injection hrv_eq' with hcrv_eq
  subst hcrv_eq
  let mid := setVarHOLFinite nm (.val (.word pw)) { pa with locals := cur.locals }
  have hmid_next : mid = { cur with
      globals := cur.globals.update (ofString "heap_ptr", .val (.word ((pw + (nw + 7)) &&& ((0 : BitVec 64) - 8)))),
      locals := mid.locals, clock := mid.clock } := by
    dsimp only [mid, setVarHOLFinite]; rw [hpa_eq]; rfl
  obtain ⟨heff_m, _, hp_al, hp_lo_sb, hp_lo_s, hp_add, hp_hi, hwok⟩ :=
    worldEff_alloc_step heff (by decide) hpw_lk hcmp1 hcmp2 hmid_next
  refine ⟨pw, nw, mid, post0, hsz_ev, by rw [hmid_next], rfl, ?_, heff_m,
    hp_al, hp_lo_sb, hp_lo_s, hp_add, hp_hi, hwok, hk, hpost⟩
  intro k hk_ne; rw [hmid_next]; simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk_ne]

theorem call0_returned_split {F : Type}
    {cur : PanSemStateFiniteExact 64 F} {fn : MlS} {args : List (ExpHOL 64)} {mid : PanSemStateFiniteExact 64 F}
    {params : List (MlS × ShapeHOL)} {fbody : ProgHOL 64} {rsh : ShapeHOL}
    (hcode : cur.code = originalRuntimeCode)
    (hlook : originalRuntimeCode.lookup fn = some (params, fbody, rsh))
    (hrun : evaluateHOLFiniteState cur (.call (some (none, none)) fn args) = (none, mid)) :
    ∃ vals callee crv cpost,
      evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) args = some vals ∧
      lookupCodeHOLFinite originalRuntimeCode.lookup fn vals = some (fbody, callee, rsh) ∧
      cur.clock ≠ 0 ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite cur callee) fbody = (some (.returned crv), cpost) ∧
      shapeEqHOL (shapeOfHOLExact crv) rsh = true ∧
      mid = { cpost.emptyLocalsHOLFinite with locals := cur.locals } := by
  rw [evaluateHOLFiniteState_call] at hrun
  rcases hargs : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) args with _ | vals
  · rw [hargs] at hrun; simp at hrun
  · rw [hargs] at hrun; dsimp only at hrun
    rcases hl : lookupCodeHOLFinite cur.code.lookup fn vals with _ | ⟨fb, fc, fr⟩
    · rw [hl] at hrun; simp at hrun
    · rw [hl] at hrun; dsimp only at hrun
      have hfb := lookupCodeHOLFinite_installed_body cur.code.lookup fn _ _ fb _ fr vals fc (by rw [hcode]; exact hlook) hl
      have hfr := lookupCodeHOLFinite_installed_return cur fn _ _ _ _ fr vals fc (by rw [hcode]; exact hlook) hl
      rw [hfb, hfr] at hl hrun
      by_cases hz : cur.clock = 0
      · rw [if_pos hz] at hrun; simp at hrun
      · rw [if_neg hz] at hrun
        rcases hc : evaluateHOLFiniteState (callEntryStateHOLFinite cur fc) fbody with ⟨rc, cpost⟩
        rw [hc] at hrun
        cases rc with
        | none => simp at hrun
        | some r1 =>
          cases r1 with
          | returned crv =>
            dsimp only at hrun
            by_cases hsh : shapeEqHOL (shapeOfHOLExact crv) rsh = true
            · rw [if_pos hsh] at hrun
              injection hrun with _ hmid
              exact ⟨vals, fc, crv, cpost, rfl, by rwa [← hcode], hz, hc, hsh, hmid.symm⟩
            · rw [if_neg hsh] at hrun; simp at hrun
          | _ => simp at hrun

theorem store_noret_dhi {F : Type} (u : PanSemStateFiniteExact 64 F) (dst val : ExpHOL 64) :
    ∀ rv, (evaluateHOLFiniteState u (.store dst val)).1 ≠ some (.returned rv) := by
  intro rv
  rw [evaluateHOLFiniteState_store]
  split <;> try simp
  split <;> try simp
  split <;> simp

theorem assign_noret_dhi {F : Type} (u : PanSemStateFiniteExact 64 F) (vk : VarKind) (nm : MlS) (val : ExpHOL 64) :
    ∀ rv, (evaluateHOLFiniteState u (.assign vk nm val)).1 ≠ some (.returned rv) := by
  intro rv
  rw [evaluateHOLFiniteState_assign]
  split <;> try simp
  split <;> simp

theorem shMemLoad_noret_dhi {F : Type} (u : PanSemStateFiniteExact 64 F) (op : OpSize) (vk : VarKind) (nm : MlS) (addr : ExpHOL 64) :
    ∀ rv, (evaluateHOLFiniteState u (.shMemLoad op vk nm addr)).1 ≠ some (.returned rv) := by
  classical
  intro rv
  rw [evaluateHOLFiniteState_shMemLoad_source]
  split
  · split
    · unfold shMemLoadHOLFiniteExact; dsimp only
      split <;> split <;> (try split) <;> simp
    · simp
  · simp

theorem store_none_evals {F : Type} (cur mid : PanSemStateFiniteExact 64 F) (dstExp valExp : ExpHOL 64)
    (hrun : evaluateHOLFiniteState cur (.store dstExp valExp) = (none, mid))
    (hdst_w : ∃ xw : BitVec 64,
      @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) dstExp = some (.val (.word xw)))
    (hval_w : ∀ v,
      @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) valExp = some v →
      ∃ vw : BitVec 64, v = .val (.word vw)) :
    ∃ xw vw : BitVec 64,
      @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) dstExp = some (.val (.word xw)) ∧
      @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) valExp = some (.val (.word vw)) ∧
      mid.locals = cur.locals ∧
      mid.globals = cur.globals ∧
      mid.code = cur.code ∧
      mid.memaddrs = cur.memaddrs ∧
      memW mid xw.toNat = vw.toNat ∧
      (∀ y : Nat, y < 2 ^ 64 → y ≠ xw.toNat → memW mid y = memW cur y) := by
  obtain ⟨xw, hdst⟩ := hdst_w
  have hrun_save := hrun
  rw [evaluateHOLFiniteState_store] at hrun
  rcases hval_ev : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) valExp with _ | vv
  · simp [hdst, hval_ev] at hrun
  · obtain ⟨vw, rfl⟩ := hval_w vv hval_ev
    obtain ⟨hm_eq, hm_ne⟩ := store_memW_eq_and_ne cur mid dstExp valExp xw vw hrun_save hdst hval_ev
    simp only [hdst, hval_ev, flattenHOL, panMemStoresHOL, panMemStoreHOL] at hrun
    by_cases hdom : cur.memaddrs xw
    · simp only [hdom, ↓reduceIte] at hrun
      injection hrun with _ hmid
      subst hmid
      exact ⟨xw, vw, hdst, rfl, rfl, rfl, rfl, rfl, hm_eq, hm_ne⟩
    · simp [hdom] at hrun

theorem ite_noret_dhi {F : Type} (u : PanSemStateFiniteExact 64 F) (c : ExpHOL 64) (p q : ProgHOL 64)
    (hp : ∀ rv, (evaluateHOLFiniteState u p).1 ≠ some (.returned rv))
    (hq : ∀ rv, (evaluateHOLFiniteState u q).1 ≠ some (.returned rv)) :
    ∀ rv, (evaluateHOLFiniteState u (.ite c p q)).1 ≠ some (.returned rv) := by
  intro rv
  rw [evaluateHOLFiniteState_ite]
  rcases @evalHOLExact 64 F _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a)) c with _ | cv
  · simp
  · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> try simp
    by_cases h0 : cw = 0#64
    · subst h0; simp; exact hq rv
    · rw [if_neg h0]; exact hp rv

theorem skip_noret_dhi {F : Type} (u : PanSemStateFiniteExact 64 F) :
    ∀ rv, (evaluateHOLFiniteState u .skip).1 ≠ some (.returned rv) := by
  intro rv; simp [evaluateHOLFiniteState_skip]

theorem seq_noret_dhi {F : Type} (u : PanSemStateFiniteExact 64 F) {a b : ProgHOL 64}
    (ha : ∀ rv, (evaluateHOLFiniteState u a).1 ≠ some (.returned rv))
    (hb : ∀ mid, evaluateHOLFiniteState u a = (none, mid) →
      ∀ rv, (evaluateHOLFiniteState mid b).1 ≠ some (.returned rv)) :
    ∀ rv, (evaluateHOLFiniteState u (.seq a b)).1 ≠ some (.returned rv) := by
  intro rv
  rw [evaluateHOLFiniteState_seq_line780]
  rcases ha0 : evaluateHOLFiniteState u a with ⟨ra, mid⟩
  rw [ha0] at ha
  cases ra with
  | none => exact hb mid ha0 rv
  | some _ => exact ha rv

theorem dec_noret_dhi {F : Type} (u : PanSemStateFiniteExact 64 F) (nm : MlS) (sh : ShapeHOL) (rhs : ExpHOL 64) (b : ProgHOL 64)
    (hb : ∀ v, (∀ rv, (evaluateHOLFiniteState (setVarHOLFinite nm v u) b).1 ≠ some (.returned rv))) :
    ∀ rv, (evaluateHOLFiniteState u (.dec nm sh rhs b)).1 ≠ some (.returned rv) := by
  intro rv
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  rcases @evalHOLExact 64 F _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a)) rhs with _ | v
  · simp
  · dsimp only
    split
    · rcases he : evaluateHOLFiniteState (setVarHOLFinite nm v u) b with ⟨rb, post0⟩
      dsimp only
      intro h; subst h
      exact hb v rv (by rw [he])
    · simp

theorem while_noret_dhi {F : Type} (st : PanSemStateFiniteExact 64 F)
    (c : ExpHOL 64) (b : ProgHOL 64)
    (hb : ∀ (u : PanSemStateFiniteExact 64 F) rv,
      (evaluateHOLFiniteState u b).1 ≠ some (.returned rv)) :
    ∀ rv, (evaluateHOLFiniteState st (.while c b)).1 ≠ some (.returned rv) := by
  suffices h : ∀ k (cur : PanSemStateFiniteExact 64 F), cur.clock = k →
      ∀ rv, (evaluateHOLFiniteState cur (.while c b)).1 ≠ some (.returned rv) from
    h st.clock st rfl
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro cur hclk rv
    rw [evaluateHOLFiniteState_while_fixClockRewrite]
    rcases hc0 : @evalHOLFinite 64 F _ cur (fun a => Classical.propDecidable (cur.memaddrs a)) c with _ | cv0
    · simp
    · rcases cv0 with ⟨⟨cw0⟩⟩ | _ | _ <;> try simp
      by_cases hwz : cw0 = 0#64
      · subst hwz; simp
      · rw [if_neg hwz]
        by_cases hkz : cur.clock = 0
        · rw [if_pos hkz]; simp
        · rw [if_neg hkz]
          have hrem0 := evaluateHOLFiniteState_clock_le (decClockHOLFinite cur) b
          rcases hb0 : evaluateHOLFiniteState (decClockHOLFinite cur) b with ⟨rb0, sb0⟩
          simp only [hb0] at hrem0 ⊢
          have hlt0 : sb0.clock < k := by change sb0.clock ≤ cur.clock - 1 at hrem0; omega
          have hnb := hb (decClockHOLFinite cur) rv
          rw [hb0] at hnb
          cases rb0 with
          | none => exact ih sb0.clock hlt0 sb0 rfl rv
          | some r0 =>
            cases r0 with
            | «continue» => exact ih sb0.clock hlt0 sb0 rfl rv
            | returned _ => exact hnb
            | _ => simp

theorem store_nobreak_dhi {F : Type} (u : PanSemStateFiniteExact 64 F) (dst val : ExpHOL 64) :
    (evaluateHOLFiniteState u (.store dst val)).1 ≠ some .break ∧
    (evaluateHOLFiniteState u (.store dst val)).1 ≠ some .continue := by
  constructor <;> {
    rw [evaluateHOLFiniteState_store]
    split <;> try simp
    split <;> try simp
    split <;> simp
  }

theorem assign_nobreak_dhi {F : Type} (u : PanSemStateFiniteExact 64 F) (vk : VarKind) (nm : MlS) (val : ExpHOL 64) :
    (evaluateHOLFiniteState u (.assign vk nm val)).1 ≠ some .break ∧
    (evaluateHOLFiniteState u (.assign vk nm val)).1 ≠ some .continue := by
  constructor <;> {
    rw [evaluateHOLFiniteState_assign]
    split <;> try simp
    split <;> simp
  }

theorem skip_nobreak_dhi {F : Type} (u : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState u .skip).1 ≠ some .break ∧
    (evaluateHOLFiniteState u .skip).1 ≠ some .continue := by
  simp [evaluateHOLFiniteState_skip]

theorem ite_nobreak_dhi {F : Type} (u : PanSemStateFiniteExact 64 F) (c : ExpHOL 64) (p q : ProgHOL 64)
    (hp : (evaluateHOLFiniteState u p).1 ≠ some .break)
    (hq : (evaluateHOLFiniteState u q).1 ≠ some .break) :
    (evaluateHOLFiniteState u (.ite c p q)).1 ≠ some .break := by
  rw [evaluateHOLFiniteState_ite]
  rcases @evalHOLExact 64 F _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a)) c with _ | cv
  · simp
  · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> try simp
    by_cases h0 : cw = 0#64
    · subst h0; simp; exact hq
    · rw [if_neg h0]; exact hp

theorem seq_nobreak_dhi {F : Type} (u : PanSemStateFiniteExact 64 F) {a b : ProgHOL 64}
    (ha : (evaluateHOLFiniteState u a).1 ≠ some .break)
    (hb : ∀ mid, evaluateHOLFiniteState u a = (none, mid) → (evaluateHOLFiniteState mid b).1 ≠ some .break) :
    (evaluateHOLFiniteState u (.seq a b)).1 ≠ some .break := by
  rw [evaluateHOLFiniteState_seq_line780]
  rcases ha0 : evaluateHOLFiniteState u a with ⟨ra, mid⟩
  rw [ha0] at ha
  cases ra with
  | none => exact hb mid ha0
  | some _ => exact ha

theorem dec_nobreak_dhi {F : Type} (u : PanSemStateFiniteExact 64 F) (nm : MlS) (sh : ShapeHOL) (rhs : ExpHOL 64) (b : ProgHOL 64)
    (hb : ∀ v, (evaluateHOLFiniteState (setVarHOLFinite nm v u) b).1 ≠ some .break) :
    (evaluateHOLFiniteState u (.dec nm sh rhs b)).1 ≠ some .break := by
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  rcases @evalHOLExact 64 F _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a)) rhs with _ | v
  · simp
  · dsimp only
    split
    · rcases he : evaluateHOLFiniteState (setVarHOLFinite nm v u) b with ⟨rb, post0⟩
      dsimp only
      intro h; subst h
      exact hb v (by rw [he])
    · simp

theorem ite_store_skip_nobreak {F : Type}
    (cur : PanSemStateFiniteExact 64 F) (cond dst val : ExpHOL 64) :
    (evaluateHOLFiniteState cur (.ite cond (.store dst val) .skip)).1 ≠ some .continue := by
  rw [evaluateHOLFiniteState_ite]
  rcases @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) cond with _ | cv
  · simp
  · rcases cv with ⟨⟨cw'⟩⟩ | _ | _ <;> try simp
    by_cases hz' : cw' = 0#64
    · subst hz'; simp [evaluateHOLFiniteState_skip]
    · rw [if_neg hz']
      split <;> try simp
      split <;> try simp
      split <;> simp

theorem seq_cont_or_none_split {F : Type}
    {cur : PanSemStateFiniteExact 64 F} {p1 p2 : ProgHOL 64}
    (hnobrk : (evaluateHOLFiniteState cur p1).1 ≠ some .continue)
    (hf : (evaluateHOLFiniteState cur (.seq p1 p2)).1 = none ∨
          (evaluateHOLFiniteState cur (.seq p1 p2)).1 = some .continue) :
    ∃ mid,
      evaluateHOLFiniteState cur p1 = (none, mid) ∧
      ((evaluateHOLFiniteState mid p2).1 = none ∨
       (evaluateHOLFiniteState mid p2).1 = some .continue) ∧
      (evaluateHOLFiniteState cur (.seq p1 p2)).2 = (evaluateHOLFiniteState mid p2).2 := by
  have hrun := evaluateHOLFiniteState_seq_line780 cur p1 p2
  rcases h0 : evaluateHOLFiniteState cur (.seq p1 p2) with ⟨r, post⟩
  rw [h0] at hf hrun
  dsimp only at hf hrun ⊢
  rcases h1 : evaluateHOLFiniteState cur p1 with ⟨r1, mid⟩
  rw [h1] at hrun
  cases r1 with
  | none =>
    dsimp only at hrun
    have hr : (evaluateHOLFiniteState mid p2).1 = r := (congrArg Prod.fst hrun).symm
    have hp : (evaluateHOLFiniteState mid p2).2 = post := (congrArg Prod.snd hrun).symm
    exact ⟨mid, rfl, hr.symm ▸ hf, hp.symm⟩
  | some r0 =>
    dsimp only at hrun
    injection hrun with hr _
    subst hr
    rcases hf with h | h
    · simp at h
    · injection h with h'; subst h'
      exact absurd (congrArg Prod.fst h1) hnobrk

theorem seq_store_fresh_returned {F : Type}
    {s cur post : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {B : List (String × Nat)}
    (heff : WorldEff s cur Rl B dhiGw)
    (bname : MlS) (bw : BitVec 64) (sz off : Nat)
    (hb : cur.locals.lookup bname = some (.val (.word bw)))
    (hlo : globN s "heap_ptr" ≤ bw.toNat)
    (hhi : bw.toNat + sz ≤ heapLimit)
    (hoff : off + 8 ≤ sz)
    (valExp : ExpHOL 64) {cont : ProgHOL 64} {rv : ValueHOL 64}
    (hword : ∀ v, @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) valExp = some v →
      ∃ w : BitVec 64, v = .val (.word w))
    (hrun : evaluateHOLFiniteState cur (.seq (.store (.op .add [.var .local bname, .const (BitVec.ofNat 64 off)]) valExp) cont) =
      (some (.returned rv), post)) :
    ∃ (mid : PanSemStateFiniteExact 64 F) (vw : BitVec 64),
      @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) valExp = some (.val (.word vw)) ∧
      mid.locals = cur.locals ∧
      mid.globals = cur.globals ∧
      WorldEff s mid Rl B dhiGw ∧
      memW mid (bw.toNat + off) = vw.toNat ∧
      (∀ y : Nat, y < 2 ^ 64 → y ≠ bw.toNat + off → memW mid y = memW cur y) ∧
      evaluateHOLFiniteState mid cont = (some (.returned rv), post) := by
  have hhl : heapLimit < 2 ^ 64 := by decide
  obtain ⟨mid, hst, hk⟩ := seq_returned_split (store_noret_dhi cur _ _) hrun
  have heff_m : WorldEff s mid Rl B dhiGw := by
    have h1 := worldEff_store_fresh_const heff bname bw sz off hb hlo hhi hoff valExp hword
    rwa [hst] at h1
  have hdst_ev : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a))
      (.op .add [.var .local bname, .const (BitVec.ofNat 64 off)]) =
      some (.val (.word (bw + BitVec.ofNat 64 off))) := by
    simp [evalHOLExact, evalListHOLExact, toExact, hb, wordOpHOL, wordOp, valueIsWord, valueWord]
  obtain ⟨xw, vw, hdst', hval_ev, hloc, hglob, _, _, hm_eq, hm_ne⟩ :=
    store_none_evals cur mid _ valExp hst ⟨_, hdst_ev⟩ hword
  rw [hdst_ev] at hdst'
  injection hdst' with h1; injection h1 with h2; injection h2 with hxw_eq
  subst hxw_eq
  have hoff_nat : (BitVec.ofNat 64 off).toNat = off := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hx_nat : (bw + BitVec.ofNat 64 off).toNat = bw.toNat + off := by
    rw [BitVec.toNat_add_of_lt] <;> omega
  rw [hx_nat] at hm_eq hm_ne
  exact ⟨mid, vw, hval_ev, hloc, hglob, heff_m, hm_eq, hm_ne, hk⟩

theorem seq_store_ssz_offs_const_returned {F : Type}
    {s cur post : PanSemStateFiniteExact 64 F} {B : List (String × Nat)}
    (hWOK : WorldOK s)
    (heff : WorldEff s cur (dhiOffsRegions s) B dhiGw)
    (off : Nat) (hoff : off + 8 ≤ 64)
    (dst valExp : ExpHOL 64) {cont : ProgHOL 64} {rv : ValueHOL 64}
    (hdst : (dst = .var .global (ofString "ssz_offs") ∧ off = 0) ∨
            dst = .op .add [.var .global (ofString "ssz_offs"), .const (BitVec.ofNat 64 off)])
    (hword : ∀ v, @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) valExp = some v →
      ∃ w : BitVec 64, v = .val (.word w))
    (hrun : evaluateHOLFiniteState cur (.seq (.store dst valExp) cont) = (some (.returned rv), post)) :
    ∃ (mid : PanSemStateFiniteExact 64 F) (vw : BitVec 64),
      @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) valExp = some (.val (.word vw)) ∧
      mid.locals = cur.locals ∧
      mid.globals = cur.globals ∧
      WorldEff s mid (dhiOffsRegions s) B dhiGw ∧
      memW mid (globN s "ssz_offs" + off) = vw.toNat ∧
      (∀ y : Nat, y < 2 ^ 64 → y ≠ globN s "ssz_offs" + off → memW mid y = memW cur y) ∧
      evaluateHOLFiniteState mid cont = (some (.returned rv), post) := by
  obtain ⟨mid, hst, hk⟩ := seq_returned_split (store_noret_dhi cur _ _) hrun
  have heff_m : WorldEff s mid (dhiOffsRegions s) B dhiGw := by
    have h1 := worldEff_store_ssz_offs_const hWOK heff off hoff dst valExp hdst hword
    rwa [hst] at h1
  have hg_kept := heff.gw_kept (ofString "ssz_offs") (by decide)
  obtain ⟨sw, hsw_s⟩ := hWOK.1.2.2.2.2.2.2.2.2.2 "ssz_offs" (by decide)
  have hsw_cur : cur.globals.lookup (ofString "ssz_offs") = some (.val (.word sw)) :=
    hg_kept.symm.trans hsw_s
  have hglob : globN s "ssz_offs" = sw.toNat := by unfold GlobalWord at hsw_s; simp [globN, hsw_s]
  have hdst_ev : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) dst =
      some (.val (.word (sw + BitVec.ofNat 64 off))) := by
    rcases hdst with ⟨rfl, rfl⟩ | rfl
    · simp [evalHOLExact, toExact, hsw_cur]
    · simp [evalHOLExact, evalListHOLExact, toExact, hsw_cur, wordOpHOL, wordOp, valueIsWord, valueWord]
  obtain ⟨xw, vw, hdst', hval_ev, hloc, hglob_eq, _, _, hm_eq, hm_ne⟩ :=
    store_none_evals cur mid dst valExp hst ⟨_, hdst_ev⟩ hword
  rw [hdst_ev] at hdst'
  injection hdst' with h1; injection h1 with h2; injection h2 with hxw_eq
  subst hxw_eq
  have hOK := dhiOffsOK_of_worldOK hWOK
  rcases hOK.2 with hg0 | ⟨hlo, hhi, _, _⟩
  · exfalso
    rw [evaluateHOLFiniteState_store] at hst
    rcases hval_ev' : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) valExp with _ | vv
    · simp [hdst_ev, hval_ev'] at hst
    · obtain ⟨vw', rfl⟩ := hword vv hval_ev'
      simp only [hdst_ev, hval_ev', flattenHOL, panMemStoresHOL, panMemStoreHOL] at hst
      have hsw0 : sw = 0#64 := BitVec.eq_of_toNat_eq (by simp; omega)
      subst hsw0
      have hndom : ¬ cur.memaddrs (0#64 + BitVec.ofNat 64 off) := by
        rw [heff.memaddrs, hWOK.1.1.memaddrs, ordinaryDomain_iff]
        have hsb : 64 < sourceBase := by decide
        have h1 : (0#64 + BitVec.ofNat 64 off).toNat = off := by simp [BitVec.toNat_ofNat]; omega
        omega
      rw [if_neg hndom] at hst
      simp at hst
  · have hhe : heapEnd < 2 ^ 64 := by decide
    have hx_nat : (sw + BitVec.ofNat 64 off).toNat = globN s "ssz_offs" + off := by
      rw [BitVec.toNat_add_of_lt]
      · simp [hglob, BitVec.toNat_ofNat]; omega
      · simp [BitVec.toNat_ofNat]; omega
    rw [hx_nat] at hm_eq hm_ne
    exact ⟨mid, vw, hval_ev, hloc, hglob_eq, heff_m, hm_eq, hm_ne, hk⟩

/-! ### `ssz_split_var_list` Return Postcondition -/

theorem ssz_split_var_list_body_returns {F : Type}
    {s entry post : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {B : List (String × Nat)}
    {wp wlen wlim : BitVec 64} {rv : ValueHOL 64}
    (heff : WorldEff s entry Rl B dhiGw)
    (hp : entry.locals.lookup (ofString "p") = some (.val (.word wp)))
    (hlen : entry.locals.lookup (ofString "len") = some (.val (.word wlen)))
    (hlim : entry.locals.lookup (ofString "lim") = some (.val (.word wlim)))
    (hrun : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_ssz_split_var_list) =
      (some (.returned rv), post)) :
    WorldEff s post Rl B dhiGw ∧
    WorldEff entry post Rl B dhiGw ∧
    ∃ (w_arr w_cnt : BitVec 64),
      rv = .rStruct [.val (.word w_arr), .val (.word w_cnt)] ∧
      w_cnt.toNat ≤ wlim.toNat ∧
      w_cnt.toNat < 2 ^ 30 ∧
      w_arr.toNat % 8 = 0 ∧
      WordsOK post (w_arr.toNat, 16 * w_cnt.toNat) ∧
      ((w_cnt.toNat = 0 ∧ w_arr.toNat = 0 ∧ wlen.toNat = 0) ∨
       (1 ≤ w_cnt.toNat ∧
        sourceBase ≤ w_arr.toNat ∧
        globN entry "heap_ptr" ≤ w_arr.toNat ∧
        w_arr.toNat + 16 * w_cnt.toNat ≤ globN post "heap_ptr" ∧
        globN post "heap_ptr" ≤ heapLimit ∧
        ∀ j : Nat, j < w_cnt.toNat → memW post (w_arr.toNat + 16 * j + 8) ≤ wlen.toNat)) := by
  have hnt : (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_ssz_split_var_list)).1 ≠ some .timeOut := by
    rw [hrun]; simp
  have hcr : ContOrRes (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_ssz_split_var_list)).1 := by
    rw [hrun]; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rv, rfl⟩)))
  have heff_s_post : WorldEff s post Rl B dhiGw := by
    have h := worldEff_ssz_split_var_list_body heff hnt hcr
    rwa [hrun] at h
  have heff_entry_refl : WorldEff entry entry Rl B dhiGw :=
    WorldEff.refl entry Rl B dhiGw heff.arena heff.code
  have heff_entry_post : WorldEff entry post Rl B dhiGw := by
    have h := worldEff_ssz_split_var_list_body heff_entry_refl hnt hcr
    rwa [hrun] at h
  dsimp only [Guest.Software.guestFn_ssz_split_var_list, sourceFnBody, sourceFunctionEntry,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hrun
  by_cases hlen0 : wlen = 0#64
  · subst hlen0
    have hite_ret : evaluateHOLFiniteState entry
        (.ite (.cmp .equal (.var .local (ofString "len")) (.const 0#64))
          (.return (.rstruct [.const 0#64, .const 0#64])) .skip) =
        (some (.returned (.rStruct [.val (.word 0#64), .val (.word 0#64)])), entry.emptyLocalsHOLFinite) := by
      rw [evaluateHOLFiniteState_ite]
      simp [evalHOLExact, evalListHOLExact, toExact, hlen, Compiler.Encoders.Asm.wordCmpHOL,
        valueIsWord, valueWord, evaluateHOLFiniteState_return, shapeOfHOLExact, sizeOfShapeWithContextHOL]
    rw [evaluateHOLFiniteState_seq_line780, hite_ret] at hrun
    dsimp only at hrun
    injection hrun with hrv hpost
    injection hrv with hrv'; injection hrv' with hrv''
    subst hrv''
    refine ⟨heff_s_post, heff_entry_post, 0#64, 0#64, rfl, Nat.zero_le _, by decide, by decide, ?_, Or.inl ⟨rfl, rfl, rfl⟩⟩
    exact ⟨rfl, rfl, fun k hk => by simp at hk⟩
  · have hite0 : evaluateHOLFiniteState entry
        (.ite (.cmp .equal (.var .local (ofString "len")) (.const 0#64))
          (.return (.rstruct [.const 0#64, .const 0#64])) .skip) = (none, entry) := by
      rw [evaluateHOLFiniteState_ite]
      simp [evalHOLExact, evalListHOLExact, toExact, hlen, Compiler.Encoders.Asm.wordCmpHOL,
        valueIsWord, valueWord, hlen0, evaluateHOLFiniteState_skip]
    rw [evaluateHOLFiniteState_seq_line780, hite0] at hrun
    dsimp only at hrun
    obtain ⟨m2, hm2, hrun2⟩ := seq_returned_split (ite_call0_noret_dhi entry _ _ _) hrun
    obtain ⟨hm2_eq, _⟩ := ite_ssz_fail_keeps entry m2 heff.code _ _ hm2
    have hm2_p : m2.locals.lookup (ofString "p") = some (.val (.word wp)) := by rw [hm2_eq]; exact hp
    have hm2_len : m2.locals.lookup (ofString "len") = some (.val (.word wlen)) := by rw [hm2_eq]; exact hlen
    have hm2_lim : m2.locals.lookup (ofString "lim") = some (.val (.word wlim)) := by rw [hm2_eq]; exact hlim
    have heff_e2 : WorldEff entry m2 Rl B dhiGw := by
      rw [hm2_eq]; exact heff_entry_refl.locals_clock _ _
    obtain ⟨v_first, p3, hv_first, _, hrun3, hp3_eq⟩ := dec_returned_split hrun2
    obtain ⟨w_first, rfl, hfirst_lt⟩ := eval_le32_word_lt m2 _ _ _ _ v_first hv_first
    let m3 := setVarHOLFinite (ofString "first") (.val (.word w_first)) m2
    have hm3_code : m3.code = originalRuntimeCode := by dsimp only [m3]; rw [hm2_eq]; exact heff.code
    obtain ⟨m4, hm4, hrun4⟩ := seq_returned_split (ite_call0_noret_dhi m3 _ _ _) hrun3
    obtain ⟨hm4_eq, hcond21⟩ := ite_ssz_fail_keeps m3 m4 hm3_code _ _ hm4
    have hm3_first : m3.locals.lookup (ofString "first") = some (.val (.word w_first)) := lookup_setVar_eq _ _ _
    have hm3_len : m3.locals.lookup (ofString "len") = some (.val (.word wlen)) := by
      dsimp only [m3]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm2_len
    have hfirst_bounds : 4 ≤ w_first.toNat ∧ w_first.toNat ≤ wlen.toNat := by
      dsimp only [evalHOLExact, evalListHOLExact, toExact] at hcond21
      rw [hm3_first, hm3_len] at hcond21
      simp only [Compiler.Encoders.Asm.wordCmpHOL, wordOpHOL, wordOp, valueIsWord, valueWord,
        List.all_cons, List.all_nil, Bool.and_self, Option.map_some, ↓reduceIte,
        List.map, List.foldr, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hcond21
      have hcond21' :
          (if (!0#64 == (if (w_first == 0#64) = true then 1#64 else 0#64) |||
              ((if (!w_first &&& (3#64 &&& ~~~0#64) == 0#64) = true then 1#64 else 0#64) |||
                ((if decide (wlen < w_first) = true then 1#64 else 0#64) ||| 0#64))) = true
            then 1#64 else 0#64) = 0#64 := hcond21
      have hne0 : w_first ≠ 0#64 := by intro hz; subst hz; simp at hcond21'
      have hmod4 : w_first.toNat % 4 = 0 := by
        have hand3 : (3#64 &&& ~~~0#64 : BitVec 64) = 3#64 := rfl
        rw [hand3] at hcond21'
        by_cases hm : (w_first &&& 3#64) == 0#64
        · have hm' : w_first &&& 3#64 = 0#64 := eq_of_beq hm
          have hn := congrArg BitVec.toNat hm'
          rw [BitVec.toNat_and] at hn
          change w_first.toNat &&& (2 ^ 2 - 1) = 0 at hn
          rwa [Nat.and_two_pow_sub_one_eq_mod _ 2] at hn
        · exfalso; simp [hm] at hcond21'; revert hcond21'; split <;> split <;> simp
      have hle_len : w_first.toNat ≤ wlen.toNat := by
        have hand3 : (3#64 &&& ~~~0#64 : BitVec 64) = 3#64 := rfl
        rw [hand3] at hcond21'
        by_cases hlt : wlen < w_first
        · exfalso; simp [hlt] at hcond21'; revert hcond21'; split <;> split <;> simp
        · simp [BitVec.lt_def] at hlt; omega
      have hf_pos : 0 < w_first.toNat := by
        by_cases hp0 : w_first.toNat = 0
        · exact absurd (BitVec.eq_of_toNat_eq hp0) hne0
        · omega
      exact ⟨by omega, hle_len⟩
    have hm4_first : m4.locals.lookup (ofString "first") = some (.val (.word w_first)) := by rw [hm4_eq]; exact hm3_first
    have hm4_p : m4.locals.lookup (ofString "p") = some (.val (.word wp)) := by
      rw [hm4_eq]; dsimp only [m3]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm2_p
    have hm4_len : m4.locals.lookup (ofString "len") = some (.val (.word wlen)) := by rw [hm4_eq]; exact hm3_len
    have hm4_lim : m4.locals.lookup (ofString "lim") = some (.val (.word wlim)) := by
      rw [hm4_eq]; dsimp only [m3]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm2_lim
    obtain ⟨v_cnt, p5, hv_cnt, _, hrun5, hp5_eq⟩ := dec_returned_split hrun4
    have hv_cnt_eq : v_cnt = .val (.word (w_first >>> 2)) := by
      simp [evalHOLExact, toExact, hm4_first, wordShiftHOL] at hv_cnt; exact hv_cnt.symm
    subst hv_cnt_eq
    let w_cnt := w_first >>> 2
    have hw_cnt_nat : w_cnt.toNat = w_first.toNat / 4 := by
      dsimp only [w_cnt]; change (w_first >>> (2 : Nat)).toNat = w_first.toNat / 4
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have hcnt_pos : 1 ≤ w_cnt.toNat := by omega
    have hcnt_lt : w_cnt.toNat < 2 ^ 30 := by omega
    let m5 := setVarHOLFinite (ofString "count") (.val (.word w_cnt)) m4
    have hm5_code : m5.code = originalRuntimeCode := by dsimp only [m5]; rw [hm4_eq]; exact hm3_code
    obtain ⟨m6, hm6, hrun6⟩ := seq_returned_split (ite_call0_noret_dhi m5 _ _ _) hrun5
    obtain ⟨hm6_eq, hcond22⟩ := ite_ssz_fail_keeps m5 m6 hm5_code _ _ hm6
    have hm5_cnt : m5.locals.lookup (ofString "count") = some (.val (.word w_cnt)) := lookup_setVar_eq _ _ _
    have hm5_lim : m5.locals.lookup (ofString "lim") = some (.val (.word wlim)) := by
      dsimp only [m5]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm4_lim
    have hcnt_le_lim : w_cnt.toNat ≤ wlim.toNat := by
      simp only [evalHOLExact, evalListHOLExact, toExact, hm5_cnt, hm5_lim,
        Compiler.Encoders.Asm.wordCmpHOL, valueIsWord, valueWord] at hcond22
      by_cases hlt : wlim < w_cnt
      · simp [hlt] at hcond22
      · simp [BitVec.lt_def] at hlt; exact hlt
    have heff_e6 : WorldEff entry m6 Rl B dhiGw := by
      have h4 : m4 = { entry with locals := m4.locals, clock := m4.clock } := by
        rw [hm4_eq]; dsimp only [m3, setVarHOLFinite]; rw [hm2_eq]
      have h6 : m6 = { entry with locals := m6.locals, clock := m6.clock } := by
        rw [hm6_eq]; dsimp only [m5, setVarHOLFinite]; rw [h4]
      rw [h6]; exact heff_entry_refl.locals_clock _ _
    have hm6_cnt : m6.locals.lookup (ofString "count") = some (.val (.word w_cnt)) := by rw [hm6_eq]; exact hm5_cnt
    have hm6_first : m6.locals.lookup (ofString "first") = some (.val (.word w_first)) := by
      rw [hm6_eq]; dsimp only [m5]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm4_first
    have hm6_p : m6.locals.lookup (ofString "p") = some (.val (.word wp)) := by
      rw [hm6_eq]; dsimp only [m5]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm4_p
    have hm6_len : m6.locals.lookup (ofString "len") = some (.val (.word wlen)) := by
      rw [hm6_eq]; dsimp only [m5]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm4_len
    obtain ⟨w_arr, nw, m7, p7, hsz_ev, _, hm7_loc, _, heff_e7, harr_al, harr_sb, harr_lo, harr_add, hhp7_hi, _, hrun7, hp7_eq⟩ :=
      decCall_alloc_returned_split heff_e6 hrun6
    have hnw_eq : nw = w_cnt * 16#64 := by
      simp [evalHOLExact, panOpHOL, evalListHOLExact, toExact, hm6_cnt, valueIsWord, valueWord] at hsz_ev
      exact hsz_ev.symm
    subst hnw_eq
    have hnw_nat : (w_cnt * 16#64).toNat = w_cnt.toNat * 16 := by
      rw [BitVec.toNat_mul, show (16#64 : BitVec 64).toNat = 16 from rfl, Nat.mod_eq_of_lt (by omega)]
    have hround16 : (w_cnt.toNat * 16 + 7) / 8 * 8 = 16 * w_cnt.toNat := by omega
    rw [hnw_nat, hround16] at harr_add
    have harr_hi : w_arr.toNat + 16 * w_cnt.toNat ≤ heapLimit := by omega
    have hhl_lt : heapLimit < 2 ^ 64 := by decide
    have hm7_cnt : m7.locals.lookup (ofString "count") = some (.val (.word w_cnt)) := by
      rw [hm7_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm6_cnt, show ofString "arr" ≠ ofString "count" by decide]
    have hm7_first : m7.locals.lookup (ofString "first") = some (.val (.word w_first)) := by
      rw [hm7_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm6_first, show ofString "arr" ≠ ofString "first" by decide]
    have hm7_arr : m7.locals.lookup (ofString "arr") = some (.val (.word w_arr)) := by
      rw [hm7_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    have hm7_p : m7.locals.lookup (ofString "p") = some (.val (.word wp)) := by
      rw [hm7_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm6_p, show ofString "arr" ≠ ofString "p" by decide]
    have hm7_len : m7.locals.lookup (ofString "len") = some (.val (.word wlen)) := by
      rw [hm7_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm6_len, show ofString "arr" ≠ ofString "len" by decide]
    obtain ⟨vi, p8, hvi, _, hrun8, hp8_eq⟩ := dec_returned_split hrun7
    have hvi0 : vi = .val (.word 0#64) := by simp [evalHOLExact] at hvi; exact hvi.symm
    subst hvi0
    let m8 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) m7
    have hm8_first : m8.locals.lookup (ofString "first") = some (.val (.word w_first)) := by
      dsimp only [m8]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm7_first
    obtain ⟨vprev, p9, hvprev, _, hrun9, hp9_eq⟩ := dec_returned_split hrun8
    have hvprev_eq : vprev = .val (.word w_first) := by
      dsimp only [evalHOLExact, toExact] at hvprev
      rw [hm8_first] at hvprev
      injection hvprev with h; exact h.symm
    subst hvprev_eq
    let m9 := setVarHOLFinite (ofString "prev") (.val (.word w_first)) m8
    obtain ⟨m10, hm10, hrun10⟩ := seq_returned_split (while_noret_dhi m9 _ _ (fun u =>
      dec_noret_dhi u _ _ _ _ (fun _ =>
        seq_noret_dhi _ (ite_call0_noret_dhi _ _ _ _) (fun sb1 _ =>
          seq_noret_dhi sb1 (ite_noret_dhi sb1 _ _ _ (store_noret_dhi sb1 _ _) (skip_noret_dhi sb1)) (fun sb2 _ =>
            seq_noret_dhi sb2 (store_noret_dhi sb2 _ _) (fun sb3 _ =>
              seq_noret_dhi sb3 (assign_noret_dhi sb3 _ _ _) (fun sb4 _ =>
                assign_noret_dhi sb4 _ _ _))))))) hrun9
    let InvRet : PanSemStateFiniteExact 64 F → Prop := fun t =>
      t.code = originalRuntimeCode ∧
      t.globals = m7.globals ∧
      t.locals.lookup (ofString "arr") = some (.val (.word w_arr)) ∧
      t.locals.lookup (ofString "count") = some (.val (.word w_cnt)) ∧
      t.locals.lookup (ofString "first") = some (.val (.word w_first)) ∧
      t.locals.lookup (ofString "p") = some (.val (.word wp)) ∧
      t.locals.lookup (ofString "len") = some (.val (.word wlen)) ∧
      (∃ wi : BitVec 64, t.locals.lookup (ofString "i") = some (.val (.word wi)) ∧ wi.toNat ≤ w_cnt.toNat ∧
        (∀ j : Nat, j + 1 < wi.toNat → memW t (w_arr.toNat + 16 * j + 8) ≤ wlen.toNat)) ∧
      (∃ wprev : BitVec 64, t.locals.lookup (ofString "prev") = some (.val (.word wprev)) ∧ wprev.toNat ≤ wlen.toNat)
    have hinv_m9 : InvRet m9 := by
      refine ⟨heff_e7.code, rfl, ?_, ?_, ?_, ?_, ?_, ⟨0#64, ?_, Nat.zero_le _, fun j hj => by simp at hj⟩,
        ⟨w_first, lookup_setVar_eq _ _ _, hfirst_bounds.2⟩⟩
      · dsimp only [m9, m8]; iterate 2 rw [lookup_setVar_ne _ _ _ _ (by decide)]
        exact hm7_arr
      · dsimp only [m9, m8]; iterate 2 rw [lookup_setVar_ne _ _ _ _ (by decide)]
        exact hm7_cnt
      · dsimp only [m9, m8]; iterate 2 rw [lookup_setVar_ne _ _ _ _ (by decide)]
        exact hm7_first
      · dsimp only [m9, m8]; iterate 2 rw [lookup_setVar_ne _ _ _ _ (by decide)]
        exact hm7_p
      · dsimp only [m9, m8]; iterate 2 rw [lookup_setVar_ne _ _ _ _ (by decide)]
        exact hm7_len
      · dsimp only [m9, m8]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact lookup_setVar_eq _ _ _
    have hloop_res := while_none_inv_dhi _ _ InvRet (fun _ h => h)
      (fun t _ =>
        dec_nobreak_dhi t _ _ _ _ (fun _ =>
          seq_nobreak_dhi _ (ite_call0_nobreak_dhi _ _ _ _).1 (fun sb1 _ =>
            seq_nobreak_dhi sb1 (ite_nobreak_dhi sb1 _ _ _ (store_nobreak_dhi sb1 _ _).1 (skip_nobreak_dhi sb1).1) (fun sb2 _ =>
              seq_nobreak_dhi sb2 (store_nobreak_dhi sb2 _ _).1 (fun sb3 _ =>
                seq_nobreak_dhi sb3 (assign_nobreak_dhi sb3 _ _ _).1 (fun sb4 _ =>
                  (assign_nobreak_dhi sb4 _ _ _).1))))))
      (fun t0 cw hcond hnz ⟨ht_code, ht_glob, ht_arr, ht_cnt, ht_first, ht_p, ht_len, ⟨wi, ht_i, hwi_le, hj_ok⟩, ⟨wprev, ht_prev, hwprev_le⟩⟩ hf => ?_)
      m9.clock m9 rfl hinv_m9 (congrArg Prod.fst hm10)
    · rw [hm10] at hloop_res
      dsimp only at hloop_res
      obtain ⟨⟨hm10_code, hm10_glob, hm10_arr, hm10_cnt, _, _, hm10_len, ⟨wi_f, hm10_i, hwi_f_le, hj_f_ok⟩, ⟨wprev_f, hm10_prev, hwprev_f_le⟩⟩, hcond_exit⟩ := hloop_res
      have h2_30_63 : (2 : Nat) ^ 30 < 2 ^ 63 := by decide
      have hwi_eq_cnt : wi_f.toNat = w_cnt.toNat := by
        have hce : @evalHOLFinite 64 F _ m10 (fun a => Classical.propDecidable (m10.memaddrs a))
            (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "count"))) =
            some (.val (.word (if wi_f.toNat < w_cnt.toNat then 1#64 else 0#64))) := by
          rw [evalHOLFinite_eq_toExact]
          simp [evalHOLExact, evalListHOLExact, toExact, hm10_i, hm10_cnt,
            Compiler.Encoders.Asm.wordCmpHOL, holAsmSignedLess_small wi_f w_cnt (by omega) (by omega)]
        have hz := hcond_exit _ hce
        by_cases hlt : wi_f.toNat < w_cnt.toNat
        · simp [hlt] at hz
        · omega
      obtain ⟨m11, hst10, hret11⟩ := seq_returned_split (store_noret_dhi m10 _ _) hrun10
      have hsub1 : (w_cnt - 1#64).toNat = w_cnt.toNat - 1 := by
        rw [BitVec.toNat_sub_of_le (by simp [BitVec.le_def]; omega)]; rfl
      have hmul16 : ((w_cnt - 1#64) * 16#64).toNat = (w_cnt.toNat - 1) * 16 := by
        rw [BitVec.toNat_mul, hsub1, show (16#64 : BitVec 64).toNat = 16 from rfl, Nat.mod_eq_of_lt (by omega)]
      have hadd_r : (((w_cnt - 1#64) * 16#64) + 8#64).toNat = (w_cnt.toNat - 1) * 16 + 8 := by
        rw [BitVec.toNat_add_of_lt]; · rw [hmul16]; rfl
        · rw [hmul16]; change (w_cnt.toNat - 1) * 16 + 8 < 2 ^ 64; omega
      have hdst10_ev : @evalHOLExact 64 F _ m10.toExact (fun a => Classical.propDecidable (m10.memaddrs a))
          (.op .add [.var .local (ofString "arr"),
            .panop .mul [.op .sub [.var .local (ofString "count"), .const 1#64], .const 16#64],
            .const 8#64]) =
          some (.val (.word (w_arr + (((w_cnt - 1#64) * 16#64) + 8#64)))) := by
        simp [evalHOLExact, panOpHOL, evalListHOLExact, toExact, hm10_arr, hm10_cnt,
          wordOpHOL, wordOp, valueIsWord, valueWord]
      have hval10_ev : @evalHOLExact 64 F _ m10.toExact (fun a => Classical.propDecidable (m10.memaddrs a))
          (.op .sub [.var .local (ofString "len"), .var .local (ofString "prev")]) =
          some (.val (.word (wlen - wprev_f))) := by
        simp [evalHOLExact, evalListHOLExact, toExact, hm10_len, hm10_prev,
          wordOpHOL, wordOp, valueIsWord, valueWord]
      obtain ⟨_, _, _, _, hm11_loc, hm11_glob, _, _, hm11_last, hm11_ne⟩ :=
        store_none_evals m10 m11 _ _ hst10 ⟨_, hdst10_ev⟩ (fun v hv => by rw [hval10_ev] at hv; injection hv with h; exact ⟨_, h.symm⟩)
      -- Wait: `store_none_evals` returns `xw` and `vw` existentially; let's just use `store_memW_eq_and_ne` + `store_none_evals`!
      obtain ⟨hm11_last_eq, hm11_ne_eq⟩ := store_memW_eq_and_ne m10 m11 _ _ _ _ hst10 hdst10_ev hval10_ev
      have hx10_nat : (w_arr + (((w_cnt - 1#64) * 16#64) + 8#64)).toNat = w_arr.toNat + 16 * (w_cnt.toNat - 1) + 8 := by
        rw [BitVec.toNat_add_of_lt] <;> omega
      have hlast_le : (wlen - wprev_f).toNat ≤ wlen.toNat := by
        rw [BitVec.toNat_sub_of_le (by simp [BitVec.le_def]; exact hwprev_f_le)]; omega
      rw [evaluateHOLFiniteState_return] at hret11
      simp only [evalHOLExact, evalListHOLExact, toExact, hm11_loc, hm10_arr, hm10_cnt,
        Option.map, List.map, shapeOfHOLExact, sizeOfShapeWithContextHOL,
        Flapjack.Pancake.PanLang.sizeOfShapesWithContextHOL, show (2 : Nat) ≤ 32 by decide, ↓reduceIte] at hret11
      injection hret11 with hrv_eq hp9_post
      injection hrv_eq with hrv_eq'
      injection hrv_eq' with hrv_eq''
      subst hrv_eq''
      have hpost_mem : post.memory = m11.memory := by
        rw [hp3_eq, hp5_eq, hp7_eq, hp8_eq, hp9_eq]; dsimp only
        rw [← hp9_post]; rfl
      have hpost_glob : post.globals = m7.globals := by
        rw [hp3_eq, hp5_eq, hp7_eq, hp8_eq, hp9_eq]; dsimp only
        rw [← hp9_post]; dsimp only [PanSemStateFiniteExact.emptyLocalsHOLFinite]
        rw [hm11_glob, hm10_glob]
      have hpost_hp : globN post "heap_ptr" = globN m7 "heap_ptr" := by
        unfold globN; rw [hpost_glob]
      have hpost_memW : ∀ a, memW post a = memW m11 a := fun a => by unfold memW; rw [hpost_mem]
      have hwok_post : WordsOK post (w_arr.toNat, 16 * w_cnt.toNat) :=
        wordsOK_preserved_of_worldEff heff_entry_post harr_al (by omega) harr_sb harr_hi
      refine ⟨heff_s_post, heff_entry_post, w_arr, w_cnt, rfl, hcnt_le_lim, hcnt_lt, harr_al, hwok_post,
        Or.inr ⟨hcnt_pos, harr_sb, harr_lo, by rw [hpost_hp]; omega, heff_entry_post.arena.2.2.1, fun j hj => ?_⟩⟩
      rw [hpost_memW]
      by_cases hj_last : j = w_cnt.toNat - 1
      · subst hj_last
        rw [← hx10_nat, hm11_last_eq]
        exact hlast_le
      · have hj_lt : j + 1 < wi_f.toNat := by omega
        have hne_addr : w_arr.toNat + 16 * j + 8 ≠ (w_arr + (((w_cnt - 1#64) * 16#64) + 8#64)).toNat := by
          rw [hx10_nat]; omega
        rw [hm11_ne_eq _ (by omega) hne_addr]
        exact hj_f_ok j hj_lt
    · -- Step of `while` loop body:
      have ht0_i : t0.locals.lookup (ofString "i") = some (.val (.word wi)) := ht_i
      have ht0_cnt : t0.locals.lookup (ofString "count") = some (.val (.word w_cnt)) := ht_cnt
      have h2_30_63 : (2 : Nat) ^ 30 < 2 ^ 63 := by decide
      have hwi_lt : wi.toNat < w_cnt.toNat := by
        rw [evalHOLFinite_eq_toExact] at hcond
        simp only [evalHOLExact, evalListHOLExact, toExact, ht0_i, ht0_cnt,
          Compiler.Encoders.Asm.wordCmpHOL,
          holAsmSignedLess_small wi w_cnt (by omega) (by omega)] at hcond
        by_cases hlt : wi.toNat < w_cnt.toNat
        · exact hlt
        · simp [hlt] at hcond; exact absurd hcond.symm hnz
      have hhl_lt : heapLimit < 2 ^ 64 := by decide
      obtain ⟨v_o, hv_o, _, hf0, hpost_o⟩ := dec_cont_or_none_split hf
      rw [hpost_o]; clear hf hpost_o
      obtain ⟨w_o, rfl, _⟩ := eval_le32_word_lt (decClockHOLFinite t0) _ _ _ _ v_o hv_o
      let u0 := setVarHOLFinite (ofString "o") (.val (.word w_o)) (decClockHOLFinite t0)
      change (evaluateHOLFiniteState u0 _).1 = _ ∨ _ at hf0
      obtain ⟨u1, hu1_ev, hf1, hpost_1⟩ := seq_cont_or_none_split (ite_call0_nobreak_dhi u0 _ _ _).2 hf0
      rw [hpost_1]; clear hf0 hpost_1
      obtain ⟨hu1_eq, hcond23⟩ := ite_ssz_fail_keeps u0 u1 ht_code _ _ hu1_ev
      have hu0_o : u0.locals.lookup (ofString "o") = some (.val (.word w_o)) := lookup_setVar_eq _ _ _
      have hu0_first : u0.locals.lookup (ofString "first") = some (.val (.word w_first)) := by
        dsimp only [u0]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact ht_first
      have hu0_len : u0.locals.lookup (ofString "len") = some (.val (.word wlen)) := by
        dsimp only [u0]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact ht_len
      have hu0_prev : u0.locals.lookup (ofString "prev") = some (.val (.word wprev)) := by
        dsimp only [u0]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact ht_prev
      have ho_bounds : wprev.toNat ≤ w_o.toNat ∧ w_o.toNat ≤ wlen.toNat := by
        dsimp only [evalHOLExact, evalListHOLExact, toExact] at hcond23
        rw [hu0_o, hu0_first, hu0_len, hu0_prev] at hcond23
        simp only [Compiler.Encoders.Asm.wordCmpHOL, wordOpHOL, wordOp, valueIsWord, valueWord,
          List.all_cons, List.all_nil, Bool.and_self, Option.map_some, ↓reduceIte,
          List.map, List.foldr, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hcond23
        have hcond23' :
            (if (!0#64 == (if decide (w_o < w_first) = true then 1#64 else 0#64) |||
                ((if decide (wlen < w_o) = true then 1#64 else 0#64) |||
                  ((if decide (w_o < wprev) = true then 1#64 else 0#64) ||| 0#64))) = true
              then 1#64 else 0#64) = 0#64 := hcond23
        have h1 : wprev.toNat ≤ w_o.toNat := by
          by_cases hlt : w_o < wprev
          · exfalso; simp [hlt] at hcond23'; revert hcond23'; split <;> split <;> simp
          · simp [BitVec.lt_def] at hlt; exact hlt
        have h2 : w_o.toNat ≤ wlen.toNat := by
          by_cases hlt : wlen < w_o
          · exfalso; simp [hlt] at hcond23'; revert hcond23'; split <;> split <;> simp
          · simp [BitVec.lt_def] at hlt; exact hlt
        exact ⟨h1, h2⟩
      have hu1_arr : u1.locals.lookup (ofString "arr") = some (.val (.word w_arr)) := by
        rw [hu1_eq]; dsimp only [u0]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact ht_arr
      have hu1_cnt : u1.locals.lookup (ofString "count") = some (.val (.word w_cnt)) := by
        rw [hu1_eq]; dsimp only [u0]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact ht_cnt
      have hu1_first : u1.locals.lookup (ofString "first") = some (.val (.word w_first)) := by
        rw [hu1_eq]; exact hu0_first
      have hu1_p : u1.locals.lookup (ofString "p") = some (.val (.word wp)) := by
        rw [hu1_eq]; dsimp only [u0]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact ht_p
      have hu1_len : u1.locals.lookup (ofString "len") = some (.val (.word wlen)) := by
        rw [hu1_eq]; exact hu0_len
      have hu1_i : u1.locals.lookup (ofString "i") = some (.val (.word wi)) := by
        rw [hu1_eq]; dsimp only [u0]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact ht_i
      have hu1_o : u1.locals.lookup (ofString "o") = some (.val (.word w_o)) := by
        rw [hu1_eq]; exact hu0_o
      have hu1_prev : u1.locals.lookup (ofString "prev") = some (.val (.word wprev)) := by
        rw [hu1_eq]; exact hu0_prev
      have hu1_memW : ∀ a, memW u1 a = memW (decClockHOLFinite t0) a := fun a => by
        unfold memW; rw [show u1.memory = u0.memory by rw [hu1_eq]]; rfl
      have hu1_code : u1.code = originalRuntimeCode := by rw [hu1_eq]; exact ht_code
      have hu1_glob : u1.globals = m7.globals := by rw [hu1_eq]; exact ht_glob
      obtain ⟨u2, hu2_ev, hf2, hpost_2⟩ := seq_cont_or_none_split (ite_store_skip_nobreak u1 _ _ _) hf1
      rw [hpost_2]; clear hf1 hpost_2
      have hu2_props : u2.locals = u1.locals ∧ u2.globals = m7.globals ∧ u2.code = originalRuntimeCode ∧
          (∀ j : Nat, j < wi.toNat → memW u2 (w_arr.toNat + 16 * j + 8) ≤ wlen.toNat) := by
        rw [evaluateHOLFiniteState_ite] at hu2_ev
        simp only [evalHOLExact, evalListHOLExact, toExact, hu1_i,
          Compiler.Encoders.Asm.wordCmpHOL, holAsmSignedLess_small 0#64 wi (by decide) (by omega),
          show (0#64 : BitVec 64).toNat = 0 from rfl] at hu2_ev
        by_cases hpos : 0 < wi.toNat
        · simp only [hpos, ↓reduceIte, show ¬ ((1#64 : BitVec 64) = 0) by decide] at hu2_ev
          have hsub1 : (wi - 1#64).toNat = wi.toNat - 1 := by
            rw [BitVec.toNat_sub_of_le (by simp [BitVec.le_def]; omega)]; rfl
          have hmul16 : ((wi - 1#64) * 16#64).toNat = (wi.toNat - 1) * 16 := by
            rw [BitVec.toNat_mul, hsub1, show (16#64 : BitVec 64).toNat = 16 from rfl, Nat.mod_eq_of_lt (by omega)]
          have hadd_r : (((wi - 1#64) * 16#64) + 8#64).toNat = (wi.toNat - 1) * 16 + 8 := by
            rw [BitVec.toNat_add_of_lt]; · rw [hmul16]; rfl
            · rw [hmul16]; change (wi.toNat - 1) * 16 + 8 < 2 ^ 64; omega
          have hdst_u1 : @evalHOLExact 64 F _ u1.toExact (fun a => Classical.propDecidable (u1.memaddrs a))
              (.op .add [.var .local (ofString "arr"),
                .panop .mul [.op .sub [.var .local (ofString "i"), .const 1#64], .const 16#64],
                .const 8#64]) =
              some (.val (.word (w_arr + (((wi - 1#64) * 16#64) + 8#64)))) := by
            simp [evalHOLExact, panOpHOL, evalListHOLExact, toExact, hu1_arr, hu1_i,
              wordOpHOL, wordOp, valueIsWord, valueWord]
          have hval_u1 : @evalHOLExact 64 F _ u1.toExact (fun a => Classical.propDecidable (u1.memaddrs a))
              (.op .sub [.var .local (ofString "o"), .var .local (ofString "prev")]) =
              some (.val (.word (w_o - wprev))) := by
            simp [evalHOLExact, evalListHOLExact, toExact, hu1_o, hu1_prev,
              wordOpHOL, wordOp, valueIsWord, valueWord]
          obtain ⟨_, _, _, _, hl2, hg2, hc2, _, _, _⟩ :=
            store_none_evals u1 u2 _ _ hu2_ev ⟨_, hdst_u1⟩ (fun v hv => by rw [hval_u1] at hv; injection hv with h; exact ⟨_, h.symm⟩)
          obtain ⟨hm2_eq', hm2_ne'⟩ := store_memW_eq_and_ne u1 u2 _ _ _ _ hu2_ev hdst_u1 hval_u1
          have hx_nat : (w_arr + (((wi - 1#64) * 16#64) + 8#64)).toNat = w_arr.toNat + 16 * (wi.toNat - 1) + 8 := by
            rw [BitVec.toNat_add_of_lt] <;> omega
          have hdiff_le : (w_o - wprev).toNat ≤ wlen.toNat := by
            rw [BitVec.toNat_sub_of_le (by simp [BitVec.le_def]; exact ho_bounds.1)]; omega
          refine ⟨hl2, hg2.trans hu1_glob, hc2.trans hu1_code, fun j hj => ?_⟩
          by_cases hjl : j = wi.toNat - 1
          · subst hjl; rw [← hx_nat, hm2_eq']; exact hdiff_le
          · have hne_j : w_arr.toNat + 16 * j + 8 ≠ (w_arr + (((wi - 1#64) * 16#64) + 8#64)).toNat := by
              rw [hx_nat]; omega
            rw [hm2_ne' _ (by omega) hne_j, hu1_memW]
            exact hj_ok j (by omega)
        · simp only [hpos, ↓reduceIte, evaluateHOLFiniteState_skip] at hu2_ev
          injection hu2_ev with _ hu2_id
          subst hu2_id
          exact ⟨rfl, hu1_glob, hu1_code, fun j hj => by omega⟩
      obtain ⟨hu2_loc, hu2_glob, hu2_code, hj_u2⟩ := hu2_props
      obtain ⟨u3, hu3_ev, hf3, hpost_3⟩ := seq_cont_or_none_split (store_nobreak_dhi u2 _ _).2 hf2
      rw [hpost_3]; clear hf2 hpost_3
      have hmul16_i : (wi * 16#64).toNat = wi.toNat * 16 := by
        rw [BitVec.toNat_mul, show (16#64 : BitVec 64).toNat = 16 from rfl, Nat.mod_eq_of_lt (by omega)]
      have hdst_u2 : @evalHOLExact 64 F _ u2.toExact (fun a => Classical.propDecidable (u2.memaddrs a))
          (.op .add [.var .local (ofString "arr"),
            .panop .mul [.var .local (ofString "i"), .const 16#64]]) =
          some (.val (.word (w_arr + (wi * 16#64)))) := by
        simp [evalHOLExact, panOpHOL, evalListHOLExact, toExact, hu2_loc, hu1_arr, hu1_i,
          wordOpHOL, wordOp, valueIsWord, valueWord]
      have hval_u2 : @evalHOLExact 64 F _ u2.toExact (fun a => Classical.propDecidable (u2.memaddrs a))
          (.op .add [.var .local (ofString "p"), .var .local (ofString "o")]) =
          some (.val (.word (wp + w_o))) := by
        simp [evalHOLExact, evalListHOLExact, toExact, hu2_loc, hu1_p, hu1_o,
          wordOpHOL, wordOp, valueIsWord, valueWord]
      obtain ⟨_, _, _, _, hu3_loc, hu3_glob, hu3_code, _, _, _⟩ :=
        store_none_evals u2 u3 _ _ hu3_ev ⟨_, hdst_u2⟩ (fun v hv => by rw [hval_u2] at hv; injection hv with h; exact ⟨_, h.symm⟩)
      obtain ⟨_, hm3_ne⟩ := store_memW_eq_and_ne u2 u3 _ _ _ _ hu3_ev hdst_u2 hval_u2
      have hx3_nat : (w_arr + (wi * 16#64)).toNat = w_arr.toNat + 16 * wi.toNat := by
        rw [BitVec.toNat_add_of_lt] <;> omega
      have hj_u3 : ∀ j : Nat, j < wi.toNat → memW u3 (w_arr.toNat + 16 * j + 8) ≤ wlen.toNat := by
        intro j hj
        have hne3 : w_arr.toNat + 16 * j + 8 ≠ (w_arr + (wi * 16#64)).toNat := by rw [hx3_nat]; omega
        rw [hm3_ne _ (by omega) hne3]
        exact hj_u2 j hj
      obtain ⟨u4, hu4_ev, _, hpost_4⟩ := seq_cont_or_none_split (assign_nobreak_dhi u3 _ _ _).2 hf3
      rw [hpost_4]; clear hf3 hpost_4
      have hu3_prev : u3.locals.lookup (ofString "prev") = some (.val (.word wprev)) := by
        rw [hu3_loc, hu2_loc]; exact hu1_prev
      have hvv_prev : u3.isValidValueHOLFinite .local (ofString "prev") (.val (.word w_o)) = true := by
        simp [PanSemStateFiniteExact.isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact,
          toExact, hu3_prev, shapeOfHOLExact, shapeEqHOL]
      rw [evaluateHOLFiniteState_assign] at hu4_ev
      simp only [evalHOLExact, toExact, hu3_loc, hu2_loc, hu1_o, hvv_prev,
        ↓reduceIte, setKvarHOLFinite] at hu4_ev
      injection hu4_ev with _ hu4_eq; subst hu4_eq
      let u4 := setVarHOLFinite (ofString "prev") (.val (.word w_o)) u3
      have hu4_i : u4.locals.lookup (ofString "i") = some (.val (.word wi)) := by
        dsimp only [u4]; rw [lookup_setVar_ne _ _ _ _ (by decide), hu3_loc, hu2_loc]; exact hu1_i
      have hvv_i : u4.isValidValueHOLFinite .local (ofString "i") (.val (.word (wi + 1#64))) = true := by
        simp [PanSemStateFiniteExact.isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact,
          toExact, hu4_i, shapeOfHOLExact, shapeEqHOL]
      have hu5_eq : (evaluateHOLFiniteState u4
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64]))).2 =
          setVarHOLFinite (ofString "i") (.val (.word (wi + 1#64))) u4 := by
        rw [evaluateHOLFiniteState_assign]
        simp [evalHOLExact, evalListHOLExact, toExact, hu4_i, wordOpHOL, wordOp, valueIsWord, valueWord,
          PanSemStateFiniteExact.isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact,
          shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite]
      rw [hu5_eq]
      let u5 := setVarHOLFinite (ofString "i") (.val (.word (wi + 1#64))) u4
      have hwi_inc : (wi + 1#64).toNat = wi.toNat + 1 := by
        rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
      refine ⟨hu3_code.trans hu2_code, hu3_glob.trans hu2_glob, ?_, ?_, ?_, ?_, ?_,
        ⟨wi + 1#64, ?_, by omega, fun j hj => ?_⟩,
        ⟨w_o, ?_, ho_bounds.2⟩⟩
      · dsimp only; rw [resVarEq_lookup_local, if_neg (by decide)]
        dsimp only [u5, u4]; iterate 2 rw [lookup_setVar_ne _ _ _ _ (by decide)]
        rw [hu3_loc, hu2_loc]; exact hu1_arr
      · dsimp only; rw [resVarEq_lookup_local, if_neg (by decide)]
        dsimp only [u5, u4]; iterate 2 rw [lookup_setVar_ne _ _ _ _ (by decide)]
        rw [hu3_loc, hu2_loc]; exact hu1_cnt
      · dsimp only; rw [resVarEq_lookup_local, if_neg (by decide)]
        dsimp only [u5, u4]; iterate 2 rw [lookup_setVar_ne _ _ _ _ (by decide)]
        rw [hu3_loc, hu2_loc]; exact hu1_first
      · dsimp only; rw [resVarEq_lookup_local, if_neg (by decide)]
        dsimp only [u5, u4]; iterate 2 rw [lookup_setVar_ne _ _ _ _ (by decide)]
        rw [hu3_loc, hu2_loc]; exact hu1_p
      · dsimp only; rw [resVarEq_lookup_local, if_neg (by decide)]
        dsimp only [u5, u4]; iterate 2 rw [lookup_setVar_ne _ _ _ _ (by decide)]
        rw [hu3_loc, hu2_loc]; exact hu1_len
      · dsimp only; rw [resVarEq_lookup_local, if_neg (by decide)]
        exact lookup_setVar_eq _ _ _
      · rw [hwi_inc] at hj
        change memW u3 (w_arr.toNat + 16 * j + 8) ≤ wlen.toNat
        exact hj_u3 j (by omega)
      · dsimp only; rw [resVarEq_lookup_local, if_neg (by decide)]
        rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact lookup_setVar_eq _ _ _

/-! ### `input_blob` & `decode_bytes_list` Return Postconditions -/

theorem shMemLoad_nobreak_dhi {F : Type} (u : PanSemStateFiniteExact 64 F)
    (op : OpSize) (vk : VarKind) (nm : MlS) (addr : ExpHOL 64) :
    (evaluateHOLFiniteState u (.shMemLoad op vk nm addr)).1 ≠ some .break ∧
    (evaluateHOLFiniteState u (.shMemLoad op vk nm addr)).1 ≠ some .continue := by
  classical
  constructor <;> {
    rw [evaluateHOLFiniteState_shMemLoad_source]
    split
    · split
      · unfold shMemLoadHOLFiniteExact; dsimp only
        split <;> split <;> (try split) <;> simp
      · simp
    · simp
  }

theorem tailCall_returned_split {F : Type}
    {cur post : PanSemStateFiniteExact 64 F}
    {fn : MlS} {args : List (ExpHOL 64)} {rv : ValueHOL 64}
    {params : List (MlS × ShapeHOL)} {fbody : ProgHOL 64} {rsh : ShapeHOL}
    (hcode : cur.code = originalRuntimeCode)
    (hlook : originalRuntimeCode.lookup fn = some (params, fbody, rsh))
    (hrun : evaluateHOLFiniteState cur (.call none fn args) = (some (.returned rv), post)) :
    ∃ vals callee cpost,
      evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) args = some vals ∧
      lookupCodeHOLFinite originalRuntimeCode.lookup fn vals = some (fbody, callee, rsh) ∧
      cur.clock ≠ 0 ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite cur callee) fbody = (some (.returned rv), cpost) ∧
      shapeEqHOL (shapeOfHOLExact rv) rsh = true ∧
      post = cpost.emptyLocalsHOLFinite := by
  rw [evaluateHOLFiniteState_call] at hrun
  rcases hargs : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) args with _ | vals
  · rw [hargs] at hrun; simp at hrun
  · rw [hargs] at hrun; dsimp only at hrun
    rcases hl : lookupCodeHOLFinite cur.code.lookup fn vals with _ | ⟨fb, fc, fr⟩
    · rw [hl] at hrun; simp at hrun
    · rw [hl] at hrun; dsimp only at hrun
      have hfb := lookupCodeHOLFinite_installed_body cur.code.lookup fn _ _ fb _ fr vals fc (by rw [hcode]; exact hlook) hl
      have hfr := lookupCodeHOLFinite_installed_return cur fn _ _ _ _ fr vals fc (by rw [hcode]; exact hlook) hl
      rw [hfb, hfr] at hl hrun
      by_cases hz : cur.clock = 0
      · rw [if_pos hz] at hrun; simp at hrun
      · rw [if_neg hz] at hrun
        rcases hc : evaluateHOLFiniteState (callEntryStateHOLFinite cur fc) fbody with ⟨rc, cpost⟩
        rw [hc] at hrun
        cases rc with
        | none => simp at hrun
        | some r1 =>
          cases r1 with
          | returned crv =>
            dsimp only at hrun
            by_cases hsh : shapeEqHOL (shapeOfHOLExact crv) rsh = true
            · rw [if_pos hsh] at hrun
              injection hrun with hrv hpost
              cases hrv
              exact ⟨vals, fc, cpost, rfl, by rwa [← hcode], hz, hc, hsh, hpost.symm⟩
            · rw [if_neg hsh] at hrun; simp at hrun
          | _ => simp at hrun

theorem eval_load_one_memW {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e : ExpHOL 64) (xw vw : BitVec 64)
    (he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e = some (.val (.word xw)))
    (hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.load .one e) = some (.val (.word vw))) :
    vw.toNat = memW s xw.toNat := by
  cases hm : s.memory xw with
  | word w =>
    by_cases hd : s.memaddrs xw
    · simp [evalHOLExact, isWfShapeExactHOL, he, memLoadHOLExact, hd, hm] at hv
      subst hv
      unfold memW
      have hbx : BitVec.ofNat 64 xw.toNat = xw := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt xw.isLt]
      simp [hbx, hm]
    · simp [evalHOLExact, isWfShapeExactHOL, he, memLoadHOLExact, hd] at hv

theorem input_blob_body_returns {F : Type}
    {s entry post : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {B : List (String × Nat)}
    {rv : ValueHOL 64}
    (heff : WorldEff s entry Rl B dhiGw)
    (hrun : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_input_blob) =
      (some (.returned rv), post)) :
    WorldEff s post Rl B dhiGw ∧
    ∃ (wp wlen : BitVec 64),
      rv = .rStruct [.val (.word wp), .val (.word wlen)] ∧
      wlen.toNat ≤ 1073741808 ∧
      sourceBase ≤ wp.toNat ∧
      wp.toNat + wlen.toNat + 8 ≤ heapLimit := by
  have hnt : (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_input_blob)).1 ≠ some .timeOut := by
    rw [hrun]; simp
  have hcr : ContOrRes (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_input_blob)).1 := by
    rw [hrun]; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rv, rfl⟩)))
  have heff_s_post : WorldEff s post Rl B dhiGw := by
    have h := worldEff_input_blob_body heff hnt hcr
    rwa [hrun] at h
  dsimp only [Guest.Software.guestFn_input_blob, sourceFnBody, sourceFunctionEntry,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hrun
  obtain ⟨vlen0, p0, hvlen0, _, hrun1, _⟩ := dec_returned_split hrun
  have hvlen0_eq : vlen0 = .val (.word 0#64) := by simp [evalHOLExact] at hvlen0; exact hvlen0.symm
  subst hvlen0_eq
  let m0 := setVarHOLFinite (ofString "len") (.val (.word 0#64)) entry
  obtain ⟨m1, hm1, hrun2⟩ := seq_returned_split (shMemLoad_noret_dhi m0 _ _ _ _) hrun1
  have heff_m1 : WorldEff s m1 Rl B dhiGw := by
    have h := worldEff_shMemLoad_local (heff.locals_clock m0.locals m0.clock) .opW (ofString "len") (ExpHOL.const 1073741832#64)
    have hm0_eq : ({ entry with locals := m0.locals, clock := m0.clock } : PanSemStateFiniteExact 64 F) = m0 := rfl
    rw [hm0_eq, hm1] at h
    exact h
  obtain ⟨wlen, hm1_eq⟩ := shMemLoad_local_none_inv m0 .opW (ofString "len") _ hm1
  have hm1_code : m1.code = originalRuntimeCode := heff_m1.code
  have hm1_len : m1.locals.lookup (ofString "len") = some (.val (.word wlen)) := by
    rw [hm1_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  obtain ⟨m2, hm2, hrun3⟩ := seq_returned_split (ite_call0_noret_dhi m1 _ _ _) hrun2
  obtain ⟨hm2_eq, hcond_le⟩ := ite_trap_with_keeps m1 m2 hm1_code _ _ hm2
  have hwlen_le : wlen.toNat ≤ 1073741808 := by
    simp only [evalHOLExact, evalListHOLExact, toExact, hm1_len,
      Compiler.Encoders.Asm.wordCmpHOL, valueIsWord, valueWord] at hcond_le
    by_cases hlt : (1073741808#64 : BitVec 64) < wlen
    · simp [hlt] at hcond_le
    · simp [BitVec.lt_def] at hlt; exact hlt
  have heff_m2 : WorldEff s m2 Rl B dhiGw := by rw [hm2_eq]; exact heff_m1
  have hm2_len : m2.locals.lookup (ofString "len") = some (.val (.word wlen)) := by
    rw [hm2_eq]; exact hm1_len
  obtain ⟨wp, nw, m3, p3, hsz_ev, _, hm3_loc, _, heff3, _, hwp_sb, _, hwp_add, hhp3_hi, _, hrun4, _⟩ :=
    decCall_alloc_returned_split heff_m2 hrun3
  have hnw_eq : nw = wlen + 8#64 := by
    simp [evalHOLExact, evalListHOLExact, toExact, hm2_len, wordOpHOL, wordOp, valueIsWord, valueWord] at hsz_ev
    exact hsz_ev.symm
  subst hnw_eq
  have hnw_nat : (wlen + 8#64).toNat = wlen.toNat + 8 := by
    rw [BitVec.toNat_add_of_lt]; · rfl
    · change wlen.toNat + 8 < 2 ^ 64; omega
  have hwp_hi : wp.toNat + wlen.toNat + 8 ≤ heapLimit := by omega
  obtain ⟨vi, p4, hvi, _, hrun5, _⟩ := dec_returned_split hrun4
  have hvi0 : vi = .val (.word 0#64) := by simp [evalHOLExact] at hvi; exact hvi.symm
  subst hvi0
  let m4 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) m3
  obtain ⟨vw, p5, hvw, _, hrun6, _⟩ := dec_returned_split hrun5
  have hvw0 : vw = .val (.word 0#64) := by simp [evalHOLExact] at hvw; exact hvw.symm
  subst hvw0
  let m5 := setVarHOLFinite (ofString "w") (.val (.word 0#64)) m4
  obtain ⟨m6, hm6, hret⟩ := seq_returned_split (while_noret_dhi m5 _ _ (fun u =>
    seq_noret_dhi u (shMemLoad_noret_dhi u _ _ _ _) (fun u1 _ =>
      seq_noret_dhi u1 (store_noret_dhi u1 _ _) (fun u2 _ =>
        assign_noret_dhi u2 _ _ _)))) hrun6
  have hm5_p : m5.locals.lookup (ofString "p") = some (.val (.word wp)) := by
    dsimp only [m5, m4]
    rw [lookup_setVar_ne _ _ _ _ (by decide), lookup_setVar_ne _ _ _ _ (by decide), hm3_loc]
    simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hm5_len : m5.locals.lookup (ofString "len") = some (.val (.word wlen)) := by
    dsimp only [m5, m4]
    rw [lookup_setVar_ne _ _ _ _ (by decide), lookup_setVar_ne _ _ _ _ (by decide), hm3_loc]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, hm2_len, show ofString "p" ≠ ofString "len" by decide]
  have hm6_p : m6.locals.lookup (ofString "p") = some (.val (.word wp)) := by
    have hk := evaluate_keepLocal (ofString "p") _ (by decide) m5 (Or.inl (congrArg Prod.fst hm6))
    rw [hm6] at hk; rw [hk]; exact hm5_p
  have hm6_len : m6.locals.lookup (ofString "len") = some (.val (.word wlen)) := by
    have hk := evaluate_keepLocal (ofString "len") _ (by decide) m5 (Or.inl (congrArg Prod.fst hm6))
    rw [hm6] at hk; rw [hk]; exact hm5_len
  rw [evaluateHOLFiniteState_return] at hret
  simp only [evalHOLExact, evalListHOLExact, toExact, hm6_p, hm6_len,
    Option.map, List.map, shapeOfHOLExact, sizeOfShapeWithContextHOL,
    Flapjack.Pancake.PanLang.sizeOfShapesWithContextHOL, show (2 : Nat) ≤ 32 by decide, ↓reduceIte] at hret
  injection hret with hrv_eq _
  injection hrv_eq with hrv_eq'
  injection hrv_eq' with hrv_eq''
  subst hrv_eq''
  exact ⟨heff_s_post, wp, wlen, rfl, hwlen_le, hwp_sb, hwp_hi⟩

theorem decode_bytes_list_body_returns {F : Type}
    {s entry post : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {B : List (String × Nat)}
    {wp wlen wlim wmaxb : BitVec 64} {rv : ValueHOL 64}
    (heff : WorldEff s entry Rl B dhiGw)
    (hp : entry.locals.lookup (ofString "p") = some (.val (.word wp)))
    (hlen : entry.locals.lookup (ofString "len") = some (.val (.word wlen)))
    (hlim : entry.locals.lookup (ofString "lim") = some (.val (.word wlim)))
    (hmaxb : entry.locals.lookup (ofString "maxb") = some (.val (.word wmaxb)))
    (hrun : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_decode_bytes_list) =
      (some (.returned rv), post)) :
    WorldEff s post Rl B dhiGw ∧
    WorldEff entry post Rl B dhiGw ∧
    ∃ (w_arr w_cnt : BitVec 64),
      rv = .rStruct [.val (.word w_arr), .val (.word w_cnt)] ∧
      w_cnt.toNat ≤ wlim.toNat ∧
      w_cnt.toNat < 2 ^ 30 ∧
      w_arr.toNat % 8 = 0 ∧
      WordsOK post (w_arr.toNat, 16 * w_cnt.toNat) ∧
      ((w_cnt.toNat = 0 ∧ w_arr.toNat = 0 ∧ wlen.toNat = 0) ∨
       (1 ≤ w_cnt.toNat ∧
        sourceBase ≤ w_arr.toNat ∧
        globN entry "heap_ptr" ≤ w_arr.toNat ∧
        w_arr.toNat + 16 * w_cnt.toNat ≤ globN post "heap_ptr" ∧
        globN post "heap_ptr" ≤ heapLimit ∧
        ∀ j : Nat, j < w_cnt.toNat → memW post (w_arr.toNat + 16 * j + 8) ≤ wlen.toNat)) := by
  have hnt : (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_decode_bytes_list)).1 ≠ some .timeOut := by
    rw [hrun]; simp
  have hcr : ContOrRes (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_decode_bytes_list)).1 := by
    rw [hrun]; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rv, rfl⟩)))
  have heff_s_post : WorldEff s post Rl B dhiGw := by
    have h := worldEff_decode_bytes_list_body heff hnt hcr
    rwa [hrun] at h
  have heff_entry_refl : WorldEff entry entry Rl B dhiGw :=
    WorldEff.refl entry Rl B dhiGw heff.arena heff.code
  have heff_entry_post : WorldEff entry post Rl B dhiGw := by
    have h := worldEff_decode_bytes_list_body heff_entry_refl hnt hcr
    rwa [hrun] at h
  dsimp only [Guest.Software.guestFn_decode_bytes_list, sourceFnBody, sourceFunctionEntry,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hrun
  obtain ⟨vals, fc, crv, cp, p0, hargs, hl, _, hc, _, _, hrun1, hp0_eq⟩ :=
    decCall_returned_split heff.code lookup_ssz_split_var_list hrun
  obtain ⟨wp', wlen', wlim', hvals_eq, hfc_p, hfc_len, hfc_lim⟩ :=
    lookupCode_three_words_any_dhi (by decide) (by decide) (by decide) lookup_ssz_split_var_list hl
  have hargs_eq : vals = [.val (.word wp), .val (.word wlen), .val (.word wlim)] := by
    rw [evalListHOLFinite_eq_toExact] at hargs
    simp [evalListHOLExact, evalHOLExact, toExact, hp, hlen, hlim] at hargs
    exact hargs.symm
  rw [hargs_eq] at hvals_eq
  injection hvals_eq with h1 htl1
  injection h1 with h1'; injection h1' with hwp_eq; subst hwp_eq
  injection htl1 with h2 htl2
  injection h2 with h2'; injection h2' with hwlen_eq; subst hwlen_eq
  injection htl2 with h3 _
  injection h3 with h3'; injection h3' with hwlim_eq; subst hwlim_eq
  obtain ⟨_, heff_ent_cp, w_arr, w_cnt, rfl, hcnt_lim, hcnt_lt, harr_al, hwok_cp, hcases⟩ :=
    ssz_split_var_list_body_returns (heff_entry_refl.locals_clock fc (entry.clock - 1)) hfc_p hfc_len hfc_lim hc
  let m1 := setVarHOLFinite (ofString "r") (.rStruct [.val (.word w_arr), .val (.word w_cnt)]) { cp with locals := entry.locals }
  obtain ⟨vi, p1, hvi, _, hrun2, hp1_eq⟩ := dec_returned_split hrun1
  have hvi0 : vi = .val (.word 0#64) := by simp [evalHOLExact] at hvi; exact hvi.symm
  subst hvi0
  let m2 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) m1
  obtain ⟨m3, hm3, hret⟩ := seq_returned_split (while_noret_dhi m2 _ _ (fun u =>
    seq_noret_dhi u (ite_call0_noret_dhi u _ _ _) (fun u1 _ => assign_noret_dhi u1 _ _ _))) hrun2
  have hm2_r : m2.locals.lookup (ofString "r") = some (.rStruct [.val (.word w_arr), .val (.word w_cnt)]) := by
    dsimp only [m2, m1]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact lookup_setVar_eq _ _ _
  have hm3_r : m3.locals.lookup (ofString "r") = some (.rStruct [.val (.word w_arr), .val (.word w_cnt)]) := by
    have hk := evaluate_keepLocal (ofString "r") _ (by decide) m2 (Or.inl (congrArg Prod.fst hm3))
    rw [hm3] at hk; rw [hk]; exact hm2_r
  have hm2_code : m2.code = originalRuntimeCode := heff_ent_cp.code
  let InvDbl : PanSemStateFiniteExact 64 F → Prop := fun t =>
    t.code = originalRuntimeCode ∧ t.memory = cp.memory ∧ t.globals = cp.globals
  have hloop_ro := while_none_inv_dhi _ _ InvDbl (fun _ h => h)
    (fun t _ => seq_nobreak_dhi t (ite_call0_nobreak_dhi t _ _ _).1 (fun u1 _ => (assign_nobreak_dhi u1 _ _ _).1))
    (fun t0 _ _ _ ⟨ht_c, ht_m, ht_g⟩ hf => ?_)
    m2.clock m2 rfl ⟨hm2_code, rfl, rfl⟩ (congrArg Prod.fst hm3)
  · rw [hm3] at hloop_ro
    obtain ⟨⟨_, hm3_mem, hm3_glob⟩, _⟩ := hloop_ro
    rw [evaluateHOLFiniteState_return] at hret
    simp only [evalHOLExact, evalListHOLExact, toExact, hm3_r,
      Option.map, List.map, shapeOfHOLExact, sizeOfShapeWithContextHOL,
      Flapjack.Pancake.PanLang.sizeOfShapesWithContextHOL, show (2 : Nat) ≤ 32 by decide, ↓reduceIte] at hret
    injection hret with hrv_eq hpost_m3
    cases hrv_eq
    have hpost_mem : post.memory = cp.memory := by
      rw [hp0_eq, hp1_eq]; dsimp only; rw [← hpost_m3]; exact hm3_mem
    have hpost_glob : post.globals = cp.globals := by
      rw [hp0_eq, hp1_eq]; dsimp only; rw [← hpost_m3]; exact hm3_glob
    have hpost_hp : globN post "heap_ptr" = globN cp "heap_ptr" := by unfold globN; rw [hpost_glob]
    have hpost_memW : ∀ a, memW post a = memW cp a := fun a => by unfold memW; rw [hpost_mem]
    refine ⟨heff_s_post, heff_entry_post, w_arr, w_cnt, rfl, hcnt_lim, hcnt_lt, harr_al, ?_, ?_⟩
    · rcases hcases with ⟨hcnt0, harr0, _⟩ | ⟨_, harr_sb, _, harr_hi, hcp_lim, _⟩
      · rw [hcnt0, harr0]; exact ⟨rfl, rfl, fun k hk => by simp at hk⟩
      · exact wordsOK_preserved_of_worldEff heff_entry_post harr_al (by omega) harr_sb (by omega)
    · rcases hcases with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4, h5, h6⟩
      · exact Or.inl ⟨h1, h2, h3⟩
      · refine Or.inr ⟨h1, h2, h3, by rw [hpost_hp]; exact h4, heff_entry_post.arena.2.2.1, fun j hj => ?_⟩
        rw [hpost_memW]; exact h6 j hj
  · obtain ⟨u1, hu1, _, hpost_a⟩ := seq_cont_or_none_split (ite_call0_nobreak_dhi (decClockHOLFinite t0) _ _ _).2 hf
    obtain ⟨hu1_eq, _⟩ := ite_ssz_fail_keeps (decClockHOLFinite t0) u1 ht_c _ _ hu1
    subst hu1_eq
    have hasg : InvDbl (evaluateHOLFiniteState (decClockHOLFinite t0)
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64]))).2 := by
      rw [evaluateHOLFiniteState_assign]
      split
      · exact ⟨ht_c, ht_m, ht_g⟩
      · split
        · exact ⟨ht_c, ht_m, ht_g⟩
        · exact ⟨ht_c, ht_m, ht_g⟩
    rwa [hpost_a]

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
