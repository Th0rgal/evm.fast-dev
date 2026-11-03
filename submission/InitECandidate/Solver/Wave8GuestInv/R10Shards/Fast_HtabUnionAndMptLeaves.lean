import InitECandidate.Solver.Wave8GuestInv.MemoryViews
import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.HtabC00Ports.SupportBase
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.ro_htab_item
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M25.nf_node_invalidate
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M26.Common

/-! Proofs for `htab_union_into_spec` and MPT leaf contracts (`Fast_HtabUnionAndMptLeaves.lean`). -/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_HtabUnionAndMptLeaves

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

def FunSpec (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop)
    (fname : MlS) : Prop :=
  ∃ (params : List (MlS × ShapeHOL)) (body : ProgHOL 64) (retShape : ShapeHOL),
    originalRuntimeCode.lookup fname = some (params, body, retShape) ∧
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → P s →
      (∃ values, lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
        some (body, s.locals, retShape)) →
      (evaluateHOLFiniteState s body).1 ≠ some .timeOut →
      Q s (evaluateHOLFiniteState s body).1 (evaluateHOLFiniteState s body).2

def OnReturn (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Prop) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop :=
  fun s r post => ∀ v, r = some (.returned v) → Q s post

theorem lookupCodeHOLFinite_installed_return {F : Type}
    (state : PanSemStateFiniteExact 64 F) (fname : MlS)
    (params : List (MlS × ShapeHOL)) (body body' : ProgHOL 64) (ret ret' : ShapeHOL)
    (values : List (ValueHOL 64)) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (hc : state.code.lookup fname = some (params, body, ret))
    (hl : lookupCodeHOLFinite state.code.lookup fname values = some (body', callee, ret')) :
    ret' = ret := by
  have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
    state.code.lookup fname values body' callee ret' hl
  simp only [Flapjack.lookupCodeHOLExact, hc] at hx
  split at hx
  · exact (congrArg (fun x => x.2.2) (Option.some.inj hx)).symm
  · cases hx

def ExitR {F : Type} (t : Nat) (s post : PanSemStateFiniteExact 64 F) : Prop :=
  let fresh : Ivl := (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr")
  ArenaReady post ∧ HtabWF post t ∧
  hdr post t 0 = hdr s t 0 ∧ hdr post t 1 = hdr s t 1 ∧
  globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
  (∀ i ∈ htabFootprint post t, Allocated post i ∧
    ((∃ j ∈ htabFootprint s t, Inside i j.1 (j.1 + j.2)) ∨ Inside i fresh.1 (fresh.1 + fresh.2))) ∧
  FrameOutside s post (htabFootprint s t) fresh ∧
  (∀ k : MlS, k ∉ (["heap_ptr"] : List String).map ofString → s.globals.lookup k = post.globals.lookup k)

theorem ExitR.toUnionExit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (h : ExitR (locN s "dst") s post) : UnionExit s post := by
  obtain ⟨hA, hW, hk0, hk1, hh, hfp, hfr, hg⟩ := h
  exact ⟨hA, hW, hk0, hk1, hh, fun i hi => (hfp i hi).1, hfr, hg⟩

theorem ExitR.refl {F : Type} (t : Nat) (s : PanSemStateFiniteExact 64 F) (hA : ArenaReady s)
    (hW : HtabWF s t) (hal : ∀ i ∈ htabFootprint s t, Allocated s i) : ExitR t s s := by
  refine ⟨hA, hW, rfl, rfl, le_refl _, fun i hi => ⟨hal i hi, Or.inl ⟨i, hi, le_refl _, le_refl _⟩⟩,
    fun _ _ _ => rfl, fun _ _ => rfl⟩

theorem ExitR.trans {F : Type} {t : Nat} {a b c : PanSemStateFiniteExact 64 F}
    (hab : ExitR t a b) (hbc : ExitR t b c) : ExitR t a c := by
  obtain ⟨_, _, hk01, hk11, hh1, hfp1, hfr1, hg1⟩ := hab
  obtain ⟨hA2, hW2, hk02, hk12, hh2, hfp2, hfr2, hg2⟩ := hbc
  refine ⟨hA2, hW2, hk02.trans hk01, hk12.trans hk11, le_trans hh1 hh2, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨hal, hprov⟩ := hfp2 i hi
    refine ⟨hal, ?_⟩
    rcases hprov with ⟨j, hj, hij⟩ | hfr
    · rcases (hfp1 j hj).2 with ⟨k, hk, hjk⟩ | hjf
      · exact Or.inl ⟨k, hk, ⟨le_trans hjk.1 hij.1, by have := hij.2; have := hjk.2; omega⟩⟩
      · right
        obtain ⟨h1, h2⟩ := hjf
        obtain ⟨h3, h4⟩ := hij
        constructor <;> simp only at * <;> omega
    · right
      obtain ⟨h1, h2⟩ := hfr
      constructor <;> simp only at * <;> omega
  · intro x hx hxf
    have hxb : ∀ j ∈ htabFootprint b t, ¬ CellHits x.toNat j := by
      intro j hj hin
      rcases (hfp1 j hj).2 with ⟨k, hk, hjk⟩ | hjf
      · exact hx k hk ⟨lt_of_le_of_lt hjk.1 hin.1, lt_of_lt_of_le hin.2 hjk.2⟩
      · apply hxf
        obtain ⟨h1, h2⟩ := hjf
        obtain ⟨h3, h4⟩ := hin
        constructor <;> simp only at * <;> omega
    have hxf2 : ¬ CellHits x.toNat (globN b "heap_ptr", globN c "heap_ptr" - globN b "heap_ptr") := by
      intro hin
      apply hxf
      obtain ⟨h3, h4⟩ := hin
      constructor <;> simp only at * <;> omega
    have hxf1 : ¬ CellHits x.toNat (globN a "heap_ptr", globN b "heap_ptr" - globN a "heap_ptr") := by
      intro hin
      apply hxf
      obtain ⟨h3, h4⟩ := hin
      constructor <;> simp only at * <;> omega
    rw [hfr2 x hxb hxf2, hfr1 x hx hxf1]
  · intro k hk
    rw [hg1 k hk, hg2 k hk]

theorem freeChain_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k nodes : Nat) :
    ∀ (Fr : List Nat) (head : Nat),
      FreeChain { s with locals := locals, clock := k } nodes head Fr ↔ FreeChain s nodes head Fr
  | [], _ => Iff.rfl
  | f :: rest, head => by
    simp only [FreeChain]
    exact and_congr Iff.rfl (freeChain_with_locals s locals k nodes rest _)

theorem htabWF_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k t : Nat) :
    HtabWF { s with locals := locals, clock := k } t ↔ HtabWF s t := by
  simp only [HtabWF, freeChain_with_locals]
  exact Iff.rfl

theorem arenaReady_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    ArenaReady { s with locals := locals, clock := k } ↔ ArenaReady s :=
  ⟨fun h => ⟨guestInv_congr (s := { s with locals := locals, clock := k }) rfl rfl rfl rfl h.1, h.2⟩,
   fun h => ⟨guestInv_with_locals_clock s locals k h.1, h.2⟩⟩

theorem exitR_locals {F : Type} (t : Nat) (a b : PanSemStateFiniteExact 64 F)
    (L1 L2 : HolFiniteMapExact MlS (ValueHOL 64)) (k1 k2 : Nat) :
    ExitR t { a with locals := L1, clock := k1 } { b with locals := L2, clock := k2 } ↔
      ExitR t a b := by
  simp only [ExitR, arenaReady_with_locals, htabWF_with_locals]
  exact Iff.rfl

theorem exitR_decClock {F : Type} (t : Nat) (a b : PanSemStateFiniteExact 64 F)
    (h : ExitR t (decClockHOLFinite a) b) : ExitR t a b := by
  have h2 : ExitR t { a with locals := a.locals, clock := a.clock - 1 }
      { b with locals := b.locals, clock := b.clock } := h
  rw [exitR_locals] at h2
  exact h2

theorem lookup_htab_set :
    originalRuntimeCode.lookup (ofString "htab_set") =
      some ([(ofString "t", .one), (ofString "key", .one), (ofString "value", .one)],
        sourceFnBody Guest.Software.guestFn_htab_set, .one) :=
  lookup_of_guestAst_getElem 138 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_set) rfl

theorem lookup_htab_union_into :
    originalRuntimeCode.lookup (ofString "htab_union_into") =
      some ([(ofString "dst", .one), (ofString "src", .one)],
        sourceFnBody Guest.Software.guestFn_htab_union_into, .one) :=
  lookup_of_guestAst_getElem 400 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_union_into) rfl

theorem locals_ext {m1 m2 : HolFiniteMapExact MlS (ValueHOL 64)}
    (h : ∀ k, m1.lookup k = m2.lookup k) : m1 = m2 := by
  cases m1; cases m2
  simp only [HolFiniteMapExact.mk.injEq]
  exact funext h

theorem FunSpec.at_lookup {Pc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Qc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop} {fname : MlS}
    (hf : FunSpec Pc Qc fname) {F : Type} (state : PanSemStateFiniteExact 64 F)
    (hcode : state.code = originalRuntimeCode) (values : List (ValueHOL 64)) (body' : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL)
    (hl : lookupCodeHOLFinite state.code.lookup fname values = some (body', callee, ret'))
    (hPc : Pc (callEntryStateHOLFinite state callee))
    (hnt : (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body').1 ≠
      some .timeOut) :
    Qc (callEntryStateHOLFinite state callee)
      (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body').1
      (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body').2 := by
  obtain ⟨params, body, ret, hlook, hspec⟩ := hf
  have hsame := lookupCodeHOLFinite_installed_body state.code.lookup fname params body body'
    ret ret' values callee (by rw [hcode]; exact hlook) hl
  have hret := lookupCodeHOLFinite_installed_return state fname params body body'
    ret ret' values callee (by rw [hcode]; exact hlook) hl
  subst hsame
  subst hret
  have hl' : lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
      some (body', (callEntryStateHOLFinite state callee).locals, ret') := by
    rw [← hcode]
    exact hl
  exact hspec _ hcode hPc ⟨values, hl'⟩ hnt

theorem locN_congr {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (n : String)
    (h : locals.lookup (ofString n) = s.locals.lookup (ofString n)) :
    locN { s with locals := locals, clock := k } n = locN s n := by
  simp only [locN, h]

theorem localsOnly_unionArgWF : LocalsOnly ["dst"] UnionArgWF := by
  intro F s locals k hl hP
  have hd := locN_congr s locals k "dst" (hl "dst" (by simp))
  simp only [UnionArgWF, htabWF_with_locals, arenaReady_with_locals] at hP ⊢
  rw [hd]
  exact hP

theorem localsOnly_htabArgWF : LocalsOnly ["t"] HtabArgWF := by
  intro F s locals k hl hP
  have ht := locN_congr s locals k "t" (hl "t" (by simp))
  simp only [HtabArgWF, htabWF_with_locals, arenaReady_with_locals] at hP ⊢
  rw [ht]
  exact hP

def UInv {F : Type} (s0 u : PanSemStateFiniteExact 64 F) : Prop :=
  u.code = originalRuntimeCode ∧
  u.locals.lookup (ofString "dst") = s0.locals.lookup (ofString "dst") ∧
  UnionArgWF u ∧ ExitR (locN s0 "dst") s0 u

theorem decCall_flow {F : Type} (s : PanSemStateFiniteExact 64 F)
    (x : MlS) (sh : ShapeHOL) (f : MlS) (args : List (ExpHOL 64)) (cont : ProgHOL 64)
    (hflow : Wave8M19.Htab.FlowR (evaluateHOLFiniteState s (.decCall x sh f args cont)).1) :
    ∃ values body' callee ret rv cpost,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values ∧
      lookupCodeHOLFinite s.code.lookup f values = some (body', callee, ret) ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' = (some (.returned rv), cpost) ∧
      Wave8M19.Htab.FlowR (evaluateHOLFiniteState (setVarHOLFinite x rv { cpost with locals := s.locals }) cont).1 ∧
      (evaluateHOLFiniteState s (.decCall x sh f args cont)).2 =
        { (evaluateHOLFiniteState (setVarHOLFinite x rv { cpost with locals := s.locals }) cont).2 with
          locals := HolFiniteMapExact.resVarEq
            (evaluateHOLFiniteState (setVarHOLFinite x rv { cpost with locals := s.locals }) cont).2.locals
            (x, s.locals.lookup x) } := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hflow ⊢
  revert hflow
  split
  · intro hf; rcases hf with h | h | h <;> cases h
  · rename_i values hargs
    split
    · intro hf; rcases hf with h | h | h <;> cases h
    · rename_i entry hl
      rcases entry with ⟨body', callee, ret⟩
      split
      · intro hf; rcases hf with h | h | h <;> cases h
      · dsimp only
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨r, cpost⟩
        rcases r with _ | r
        · intro hf; rcases hf with h | h | h <;> cases h
        · cases r with
          | returned rv =>
            dsimp only
            split
            · intro hf
              exact ⟨values, body', callee, ret, rv, cpost, hargs, hl, hrun, hf, rfl⟩
            · intro hf; rcases hf with h | h | h <;> cases h
          | _ => intro hf; rcases hf with h | h | h <;> cases h

theorem assign_local_flow {F : Type} (s : PanSemStateFiniteExact 64 F) (x : MlS) (e : ExpHOL 64)
    (hflow : Wave8M19.Htab.FlowR (evaluateHOLFiniteState s (.assign .local x e)).1) :
    ∃ v, Wave8M19.Htab.ev s e = some v ∧
      evaluateHOLFiniteState s (.assign .local x e) = (none, setVarHOLFinite x v s) := by
  rw [evaluateHOLFiniteState_assign] at hflow ⊢
  revert hflow
  split
  · intro hf; rcases hf with h | h | h <;> cases h
  · rename_i v hv
    split
    · intro _; exact ⟨v, hv, rfl⟩
    · intro hf; rcases hf with h | h | h <;> cases h

theorem seq_flow_split {F : Type} (s : PanSemStateFiniteExact 64 F) (a b : ProgHOL 64)
    (hflow : Wave8M19.Htab.FlowR (evaluateHOLFiniteState s (.seq a b)).1) :
    (∃ mid, evaluateHOLFiniteState s a = (none, mid) ∧
      Wave8M19.Htab.FlowR (evaluateHOLFiniteState mid b).1 ∧
      evaluateHOLFiniteState s (.seq a b) = evaluateHOLFiniteState mid b) ∨
    ((evaluateHOLFiniteState s a).1 ≠ none ∧
      Wave8M19.Htab.FlowR (evaluateHOLFiniteState s a).1 ∧
      evaluateHOLFiniteState s (.seq a b) = evaluateHOLFiniteState s a) := by
  rw [evaluateHOLFiniteState_seq_line780] at hflow ⊢
  rcases ha : evaluateHOLFiniteState s a with ⟨r, mid⟩
  rw [ha] at hflow ⊢
  cases r with
  | none => exact Or.inl ⟨mid, rfl, hflow, rfl⟩
  | some r' => exact Or.inr ⟨by simp, hflow, rfl⟩

theorem ite_flow_split {F : Type} (s : PanSemStateFiniteExact 64 F) (c : ExpHOL 64) (y n : ProgHOL 64)
    (hflow : Wave8M19.Htab.FlowR (evaluateHOLFiniteState s (.ite c y n)).1) :
    (Wave8M19.Htab.FlowR (evaluateHOLFiniteState s y).1 ∧
      evaluateHOLFiniteState s (.ite c y n) = evaluateHOLFiniteState s y) ∨
    (Wave8M19.Htab.FlowR (evaluateHOLFiniteState s n).1 ∧
      evaluateHOLFiniteState s (.ite c y n) = evaluateHOLFiniteState s n) := by
  rw [evaluateHOLFiniteState_ite] at hflow ⊢
  revert hflow
  split
  · split
    · intro hf; exact Or.inr ⟨hf, rfl⟩
    · intro hf; exact Or.inl ⟨hf, rfl⟩
  · intro hf; rcases hf with h | h | h <;> cases h

theorem call_htab_set_step
    (hset : FunSpec HtabArgWF (OnReturn HtabExit) (ofString "htab_set"))
    {F : Type} (st : PanSemStateFiniteExact 64 F) (rest : List (ExpHOL 64))
    (hcode : st.code = originalRuntimeCode) (hU : UnionArgWF st)
    (hflow : Wave8M19.Htab.FlowR (evaluateHOLFiniteState st
      (.call (some (none, none)) (ofString "htab_set") (.var .local (ofString "dst") :: rest))).1) :
    let post := (evaluateHOLFiniteState st
      (.call (some (none, none)) (ofString "htab_set") (.var .local (ofString "dst") :: rest))).2
    post.code = originalRuntimeCode ∧
    post.locals = st.locals ∧
    UnionArgWF post ∧
    ExitR (locN st "dst") st post := by
  intro post
  have hnr := Wave8M19.Htab.call0_noRetBrk st (ofString "htab_set") (.var .local (ofString "dst") :: rest)
  have hflow2 : (evaluateHOLFiniteState st
      (.call (some (none, none)) (ofString "htab_set") (.var .local (ofString "dst") :: rest))).1 = none ∨
    (evaluateHOLFiniteState st
      (.call (some (none, none)) (ofString "htab_set") (.var .local (ofString "dst") :: rest))).1 = some .continue := by
    rcases hflow with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hnr.1.2
  obtain ⟨values, body', callee, ret, v, cpost, hargs, hl, hrun, heq⟩ :=
    Wave8M19.Htab.call0_flow st _ _ hflow2
  obtain ⟨tv, vs, rfl, htv⟩ := Wave8M19.Htab.evalList_cons_inv st _ _ hargs
  obtain ⟨_, hct⟩ := Wave8M19.Htab.lookupCodeHOLFinite_param_at st.code.lookup (ofString "htab_set") []
    (ofString "t") .one [(ofString "key", .one), (ofString "value", .one)] _ _
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ (rfl | rfl) <;> decide)
    (by rw [hcode]; simpa using lookup_htab_set) (vpre := []) (by simp) hl
  have hcalleeT : callee.lookup (ofString "t") = st.locals.lookup (ofString "dst") := by
    rw [hct]
    simp only [evalHOLExact] at htv
    exact htv.symm
  have htE : locN (callEntryStateHOLFinite st callee) "t" = locN st "dst" := by
    simp only [locN, callEntryStateHOLFinite, hcalleeT]
  have hE : HtabArgWF (callEntryStateHOLFinite st callee) := by
    obtain ⟨hA, hW, hal⟩ := hU
    refine ⟨(arenaReady_with_locals st callee (st.clock - 1)).2 hA, ?_, ?_⟩
    · rw [htE]; exact (htabWF_with_locals st callee (st.clock - 1) _).2 hW
    · rw [htE]; exact hal
  have hnt : (evaluateHOLFiniteState (callEntryStateHOLFinite st callee) body').1 ≠ some .timeOut := by
    rw [hrun]; simp
  have hx := FunSpec.at_lookup hset st hcode _ body' callee ret hl hE hnt
  rw [hrun] at hx
  have hx' : ExitR (locN (callEntryStateHOLFinite st callee) "t")
      (callEntryStateHOLFinite st callee) cpost := hx v rfl
  rw [htE] at hx'
  have hpost : post = { cpost with locals := st.locals } := heq
  have hxR : ExitR (locN st "dst") st post := by
    have h2 : ExitR (locN st "dst") { st with locals := callee, clock := st.clock - 1 }
        { cpost with locals := cpost.locals, clock := cpost.clock } := hx'
    rw [exitR_locals] at h2
    rw [hpost]
    show ExitR (locN st "dst") { st with locals := st.locals, clock := st.clock }
      { cpost with locals := st.locals, clock := cpost.clock }
    rw [exitR_locals]
    exact h2
  obtain ⟨hAR, hWF, _, _, _, hfoot, _, _⟩ := hxR
  have hcodeP : post.code = originalRuntimeCode :=
    (PanRunBounded.evaluateHOLFiniteState_metadata st _).1.trans hcode
  refine ⟨hcodeP, by rw [hpost], ?_, hxR⟩
  have hdst_post : locN post "dst" = locN st "dst" := by
    simp only [locN, hpost]
  refine ⟨hAR, ?_, ?_⟩
  · rw [hdst_post]; exact hWF
  · rw [hdst_post]; intro i hi; exact (hfoot i hi).1

theorem union_iter
    (hset : FunSpec HtabArgWF (OnReturn HtabExit) (ofString "htab_set"))
    (itemArgs : List (ExpHOL 64)) (cond : ExpHOL 64) (setRest : List (ExpHOL 64))
    (incExp : ExpHOL 64)
    {F : Type} (s0 x : PanSemStateFiniteExact 64 F)
    (hx : UInv s0 x)
    (hflow : Wave8M19.Htab.FlowR (evaluateHOLFiniteState (decClockHOLFinite x)
      (.decCall (ofString "s") (.comb [.one, .one, .one]) (ofString "htab_item") itemArgs
        (.seq
          (.ite cond
            (.call (some (none, none)) (ofString "htab_set")
              (.var .local (ofString "dst") :: setRest))
            .skip)
          (.assign .local (ofString "i") incExp)))).1) :
    UInv s0 (evaluateHOLFiniteState (decClockHOLFinite x)
      (.decCall (ofString "s") (.comb [.one, .one, .one]) (ofString "htab_item") itemArgs
        (.seq
          (.ite cond
            (.call (some (none, none)) (ofString "htab_set")
              (.var .local (ofString "dst") :: setRest))
            .skip)
          (.assign .local (ofString "i") incExp)))).2 := by
  obtain ⟨hxcode, hxdst, hxU, hxR⟩ := hx
  obtain ⟨values, body', callee, ret, rv, cpost, hargs, hl, hrun, hcont, hpost⟩ :=
    decCall_flow (decClockHOLFinite x) _ _ _ _ _ hflow
  have hro : FunSpec GuestInv
      (fun s r post => Wave8Contracts.M15.Resumes r →
        post = { s with locals := post.locals, clock := post.clock })
      (ofString "htab_item") := Wave8Contracts.M15.ro_htab_item
  have hceG : GuestInv (callEntryStateHOLFinite (decClockHOLFinite x) callee) :=
    guestInv_with_locals_clock x callee _ hxU.1.1
  have hnt_item : (evaluateHOLFiniteState (callEntryStateHOLFinite (decClockHOLFinite x) callee) body').1 ≠
      some .timeOut := by rw [hrun]; simp
  have hitem := FunSpec.at_lookup hro (decClockHOLFinite x) hxcode values body' callee ret hl hceG hnt_item
  rw [hrun] at hitem
  have hcpost_eq : cpost = { x with locals := cpost.locals, clock := cpost.clock } :=
    hitem (Or.inl ⟨rv, rfl⟩)
  set s1 := setVarHOLFinite (ofString "s") rv { cpost with locals := x.locals } with hs1
  have hs1_eq : s1 = { x with locals := (x.locals.update (ofString "s", rv)), clock := cpost.clock } := by
    rw [hs1, hcpost_eq]; rfl
  have hs1_code : s1.code = originalRuntimeCode := by rw [hs1_eq]; exact hxcode
  have hs1_dst : s1.locals.lookup (ofString "dst") = s0.locals.lookup (ofString "dst") := by
    rw [hs1_eq]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "s" ≠ ofString "dst" by decide, hxdst]
  have hs1_U : UnionArgWF s1 := by
    rw [hs1_eq]
    exact localsOnly_unionArgWF x _ _ (fun n hn => by
      simp at hn; subst hn
      simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "s" ≠ ofString "dst" by decide]) hxU
  have hs1_R : ExitR (locN s0 "dst") s0 s1 := by
    rw [hs1_eq]
    have h2 : ExitR (locN s0 "dst") { s0 with locals := s0.locals, clock := s0.clock }
        { x with locals := x.locals.update (ofString "s", rv), clock := cpost.clock } := by
      rw [exitR_locals]; exact hxR
    exact h2
  have h_ite_step : ∀ mid,
      Wave8M19.Htab.FlowR (evaluateHOLFiniteState s1
        (.ite cond
          (.call (some (none, none)) (ofString "htab_set")
            (.var .local (ofString "dst") :: setRest))
          .skip)).1 →
      mid = (evaluateHOLFiniteState s1
        (.ite cond
          (.call (some (none, none)) (ofString "htab_set")
            (.var .local (ofString "dst") :: setRest))
          .skip)).2 →
      mid.code = originalRuntimeCode ∧
      mid.locals = s1.locals ∧
      UnionArgWF mid ∧
      ExitR (locN s0 "dst") s0 mid := by
    intro mid hif hmid_eq
    rcases ite_flow_split s1 _ _ _ hif with ⟨hyf, hyeq⟩ | ⟨hnf, hneq⟩
    · rw [hyeq] at hmid_eq
      subst hmid_eq
      obtain ⟨hcd, hlc, hUp, hRp⟩ := call_htab_set_step hset s1 _ hs1_code hs1_U hyf
      have hdst1 : locN s1 "dst" = locN s0 "dst" := by simp only [locN, hs1_dst]
      rw [hdst1] at hRp
      exact ⟨hcd, hlc, hUp, hs1_R.trans hRp⟩
    · rw [hneq, evaluateHOLFiniteState_skip] at hmid_eq
      subst hmid_eq
      exact ⟨hs1_code, rfl, hs1_U, hs1_R⟩
  rcases seq_flow_split s1 _ _ hcont with ⟨mid, hmid_none, hbf, hseq_eq⟩ | ⟨hmid_ne, hif, hseq_eq⟩
  · have hmid_inv := h_ite_step mid (Or.inl (by rw [hmid_none])) (by rw [hmid_none])
    obtain ⟨hm_code, hm_loc, hm_U, hm_R⟩ := hmid_inv
    obtain ⟨iv, _, hasg_eq⟩ := assign_local_flow mid _ _ hbf
    set fin := (evaluateHOLFiniteState (decClockHOLFinite x) _).2
    have hfin_eq : fin = { (setVarHOLFinite (ofString "i") iv mid) with
        locals := HolFiniteMapExact.resVarEq
          (setVarHOLFinite (ofString "i") iv mid).locals
          (ofString "s", x.locals.lookup (ofString "s")) } := by
      show (evaluateHOLFiniteState (decClockHOLFinite x) _).2 = _
      rw [hpost, hseq_eq, hasg_eq]
      rfl
    have hfin_code : fin.code = originalRuntimeCode := by rw [hfin_eq]; exact hm_code
    have hfin_dst : fin.locals.lookup (ofString "dst") = s0.locals.lookup (ofString "dst") := by
      rw [hfin_eq, PanRunBounded.resVarEq_lookup]
      simp [show ofString "dst" ≠ ofString "s" by decide, setVarHOLFinite,
        HolFiniteMapExact.lookup_update, FUPDATE, show ofString "i" ≠ ofString "dst" by decide,
        hm_loc, hs1_dst]
    have hfin_U : UnionArgWF fin := by
      rw [hfin_eq]
      exact localsOnly_unionArgWF mid _ _ (fun n hn => by
        simp at hn; subst hn
        rw [PanRunBounded.resVarEq_lookup]
        simp [show ofString "dst" ≠ ofString "s" by decide, setVarHOLFinite,
          HolFiniteMapExact.lookup_update, FUPDATE, show ofString "i" ≠ ofString "dst" by decide]) hm_U
    have hfin_R : ExitR (locN s0 "dst") s0 fin := by
      rw [hfin_eq]
      have h2 : ExitR (locN s0 "dst") { s0 with locals := s0.locals, clock := s0.clock }
          { mid with locals := HolFiniteMapExact.resVarEq
              (setVarHOLFinite (ofString "i") iv mid).locals
              (ofString "s", x.locals.lookup (ofString "s")), clock := mid.clock } := by
        rw [exitR_locals]; exact hm_R
      exact h2
    exact ⟨hfin_code, hfin_dst, hfin_U, hfin_R⟩
  · have hmid_inv := h_ite_step _ hif rfl
    obtain ⟨hm_code, hm_loc, hm_U, hm_R⟩ := hmid_inv
    set fin := (evaluateHOLFiniteState (decClockHOLFinite x) _).2
    have hfin_eq : fin = { (evaluateHOLFiniteState s1
        (.ite cond
          (.call (some (none, none)) (ofString "htab_set")
            (.var .local (ofString "dst") :: setRest))
          .skip)).2 with
        locals := HolFiniteMapExact.resVarEq
          (evaluateHOLFiniteState s1
            (.ite cond
              (.call (some (none, none)) (ofString "htab_set")
                (.var .local (ofString "dst") :: setRest))
              .skip)).2.locals
          (ofString "s", x.locals.lookup (ofString "s")) } := by
      show (evaluateHOLFiniteState (decClockHOLFinite x) _).2 = _
      rw [hpost, hseq_eq]
      rfl
    have hfin_code : fin.code = originalRuntimeCode := by rw [hfin_eq]; exact hm_code
    have hfin_dst : fin.locals.lookup (ofString "dst") = s0.locals.lookup (ofString "dst") := by
      rw [hfin_eq, PanRunBounded.resVarEq_lookup]
      simp [show ofString "dst" ≠ ofString "s" by decide, hm_loc, hs1_dst]
    have hfin_U : UnionArgWF fin := by
      rw [hfin_eq]
      exact localsOnly_unionArgWF _ _ _ (fun n hn => by
        simp at hn; subst hn
        rw [PanRunBounded.resVarEq_lookup]
        simp [show ofString "dst" ≠ ofString "s" by decide]) hm_U
    have hfin_R : ExitR (locN s0 "dst") s0 fin := by
      rw [hfin_eq]
      have h2 : ExitR (locN s0 "dst") { s0 with locals := s0.locals, clock := s0.clock }
          { (evaluateHOLFiniteState s1 _).2 with locals := _, clock := (evaluateHOLFiniteState s1 _).2.clock } := by
        rw [exitR_locals]; exact hm_R
      exact h2
    exact ⟨hfin_code, hfin_dst, hfin_U, hfin_R⟩

theorem htab_union_into_spec_of
    (hset : FunSpec HtabArgWF (OnReturn HtabExit) (ofString "htab_set")) :
    FunSpec UnionArgWF (OnReturn UnionExit) (ofString "htab_union_into") := by
  refine ⟨_, _, _, lookup_htab_union_into, ?_⟩
  intro F s0 hcode hP _ _ v hv
  have hb : sourceFnBody Guest.Software.guestFn_htab_union_into =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_htab_union_into).body := rfl
  suffices key : Wave8M19.Htab.Ret s0 (sourceFnBody Guest.Software.guestFn_htab_union_into)
      (fun _ post => UnionExit s0 post) from key v hv
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_htab_union_into,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map]
  apply Wave8M19.Htab.Ret.dec
  intro capv _
  set s1 := setVarHOLFinite (ofString "cap") capv s0 with hs1
  apply Wave8M19.Htab.Ret.dec
  intro iv _
  set s2 := setVarHOLFinite (ofString "i") iv s1 with hs2
  have hI2 : UInv s0 s2 := by
    refine ⟨hcode, ?_, ?_, ?_⟩
    · simp [hs2, hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "i" ≠ ofString "dst" by decide, show ofString "cap" ≠ ofString "dst" by decide]
    · exact LocalsOnly.setVar localsOnly_unionArgWF
        (by simp only [List.mem_singleton]; rintro _ rfl; decide) iv s1
        (LocalsOnly.setVar localsOnly_unionArgWF
          (by simp only [List.mem_singleton]; rintro _ rfl; decide) capv s0 hP)
    · have h0 : ExitR (locN s0 "dst") s0 s0 := ExitR.refl _ s0 hP.1 hP.2.1 hP.2.2
      have h2 : ExitR (locN s0 "dst") { s0 with locals := s0.locals, clock := s0.clock }
          { s0 with locals := s2.locals, clock := s0.clock } := by
        rw [exitR_locals]; exact h0
      exact h2
  apply Wave8M19.Htab.Ret.seq
  · intro w hw
    exfalso
    have hnr : Wave8M19.Htab.NoRet
        (.decCall (ofString "s") (.comb [.one, .one, .one]) (ofString "htab_item")
          [.var .local (ofString "src"), .var .local (ofString "i")]
          (.seq
            (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "s"))) (.const 0))
              (.call (some (none, none)) (ofString "htab_set")
                [.var .local (ofString "dst"),
                 .rfield 1 (.var .local (ofString "s")),
                 .rfield 2 (.var .local (ofString "s"))])
              .skip)
            (.assign .local (ofString "i")
              (.op .add [.var .local (ofString "i"), .const 1])))) :=
      Wave8M19.Htab.NoRet.decCall (Wave8M19.Htab.NoRet.seq
        (Wave8M19.Htab.NoRet.ite Wave8M19.Htab.NoRet.call0 Wave8M19.Htab.NoRet.skip)
        Wave8M19.Htab.NoRet.assign)
    exact Wave8M19.Htab.while_noRet _ _ (fun st v => hnr st v) _ s2 le_rfl w hw
  · intro u hu
    apply Wave8M19.Htab.Ret.ret
    intro val _
    have hIu : UInv s0 u := by
      have := Wave8M19.Htab.while_inv (UInv s0) _ _
        (fun x hx _ hfl => union_iter hset _ _ _ _ s0 x hx hfl) s2.clock s2 le_rfl hI2 (by rw [hu])
      rw [hu] at this
      exact this
    obtain ⟨_, _, _, hR⟩ := hIu
    apply ExitR.toUnionExit
    have h2 : ExitR (locN s0 "dst") { s0 with locals := s0.locals, clock := s0.clock }
        { u with locals := u.locals, clock := u.clock } := hR
    rw [← exitR_locals (L1 := s0.locals) (k1 := s0.clock)
      (L2 := HolFiniteMapExact.resVarEq
        (HolFiniteMapExact.resVarEq (emptyLocalsHOLFinite u).locals
          (ofString "i", s1.locals.lookup (ofString "i")))
        (ofString "cap", s0.locals.lookup (ofString "cap")))
      (k2 := u.clock)] at h2
    exact h2

/-! ## MPT Callee Contracts (from `ContractParts/C08.lean`) -/

def Resumes (r : Option (PanSemResultExact 64)) : Prop :=
  (∃ v, r = some (.returned v)) ∨ ∃ e v, r = some (.exception e v) ∧ e ≠ ofString "TrapErr"

def NodeKind {F : Type} (s : PanSemStateFiniteExact 64 F) (Nd : List Nat) (x : String) (k : Nat) :
    Prop :=
  locN s x ∈ Nd ∧ memW s (locN s x) = k

def NodeArgs (names : List String)
    (req : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Nat → Prop) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ ∃ Nd, NodeHeap s Nd ∧ (∀ n ∈ names, RootIn Nd (locN s n)) ∧ req s Nd

def NodeFnExit (names : List String)
    (req : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Nat → Prop) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F →
    Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop :=
  fun s r post => Resumes r → ArenaReady post ∧ globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
    globN post "scratch_ptr" ≤ globN s "scratch_ptr" ∧
    ∀ Nd, NodeHeap s Nd → (∀ n ∈ names, RootIn Nd (locN s n)) → req s Nd →
      ∃ Nd', NodeHeap post Nd' ∧ (∀ n ∈ Nd, n ∈ Nd') ∧
        (∀ n ∈ Nd, memW post n = memW s n) ∧
        (∀ n ∈ Nd', n ∈ Nd ∨ Inside (nodeIvl post n) (globN s "heap_ptr") (globN post "heap_ptr")) ∧
        FrameOutside s post
          ((Nd.map fun n => nodeIvl s n) ++
            [(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")])
          (globN s "heap_ptr", heapLimit - globN s "heap_ptr") ∧
        (∀ k : MlS, k ∉ (["heap_ptr", "scratch_ptr"] : List String).map ofString →
          s.globals.lookup k = post.globals.lookup k) ∧
        ∀ v, r = some (.returned v) → ∃ w : BitVec 64, v = .val (.word w) ∧ RootIn Nd' w.toNat

def NodeFn (names : List String)
    (req : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Nat → Prop) (fname : MlS) : Prop :=
  FunSpec (NodeArgs names req) (NodeFnExit names req) fname

def RetNibbles (fname : MlS) : Prop :=
  FunSpec ArenaReady (fun s r post => ∀ v, r = some (.returned v) →
    ∃ p l : BitVec 64, v = .rStruct [.val (.word p), .val (.word l)] ∧
      NibblesOK post p.toNat l.toNat ∧
      (locN s "klen" ≤ 32 → l.toNat ≤ 64) ∧
      Inside (p.toNat, l.toNat) (globN s "heap_ptr") (globN post "heap_ptr")) fname

theorem nf_node_invalidate :
    NodeFn ["nd"] (fun _ _ => True) (ofString "node_invalidate") :=
  InitECandidate.Solver.Wave8Contracts.M25.nf_node_invalidate

/-! ## `NoExn` and Node Constructor Helpers (`nf_node_new_ext`, `nf_node_new_leaf`) -/

def NoExn (p : ProgHOL 64) : Prop :=
  ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
    Resumes (evaluateHOLFiniteState s p).1 →
    ∃ v, (evaluateHOLFiniteState s p).1 = some (.returned v)

theorem not_resumes_none : ¬ Resumes none := by
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h

theorem not_resumes_error : ¬ Resumes (some .error) := by
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h

theorem not_resumes_timeout : ¬ Resumes (some .timeOut) := by
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h

theorem not_resumes_continue : ¬ Resumes (some .continue) := by
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h

theorem not_resumes_break : ¬ Resumes (some .break) := by
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h

theorem NoExn.store (d e : ExpHOL 64) : NoExn (.store d e) := by
  intro F s _ hr
  rw [evaluateHOLFiniteState_store] at hr
  revert hr
  split
  · split
    · split
      · intro h; exact absurd h not_resumes_none
      · intro h; exact absurd h not_resumes_error
    · intro h; exact absurd h not_resumes_error
  · intro h; exact absurd h not_resumes_error

theorem NoExn.ret (e : ExpHOL 64) : NoExn (.return e) := by
  intro F s _ hr
  rcases hr with ⟨v, hv⟩ | ⟨ex, v, hv, _⟩
  · exact ⟨v, hv⟩
  · rw [evaluateHOLFiniteState_return] at hv
    revert hv
    split
    · simp
    · split <;> simp

theorem NoExn.seq {a b : ProgHOL 64}
    (ha : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
      Resumes (evaluateHOLFiniteState s a).1 → False)
    (hb : NoExn b) : NoExn (.seq a b) := by
  intro F s hc hr
  have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata s a).1
  rw [evaluateHOLFiniteState_seq_line780] at hr ⊢
  rcases h1 : evaluateHOLFiniteState s a with ⟨r1, mid⟩
  rw [h1] at hr hmeta ⊢
  cases r1 with
  | none => exact hb mid (hmeta.trans hc) hr
  | some r' => exact False.elim (ha s hc (by rw [h1]; exact hr))

theorem alloc_body_noExn {F : Type} (st : PanSemStateFiniteExact 64 F)
    (hc : st.code = originalRuntimeCode)
    (hr : Resumes (evaluateHOLFiniteState st (sourceFnBody Guest.Software.guestFn_alloc)).1) :
    ∃ v, (evaluateHOLFiniteState st (sourceFnBody Guest.Software.guestFn_alloc)).1 = some (.returned v) := by
  rcases hr with ⟨v, hv⟩ | ⟨ex, v, hex, hne⟩
  · exact ⟨v, hv⟩
  · exfalso
    have hbody : sourceFnBody Guest.Software.guestFn_alloc =
        .dec (ofString "p") .one (.var .global (ofString "heap_ptr"))
          (.seq
            (.ite (.cmp .lower (.op .sub [.const Wave8Contracts.M26.cMax, .var .local (ofString "p")])
                (.var .local (ofString "n")))
              (.call (some (none, none)) (ofString "trap_with") [.const 1])
              .skip)
            (.dec (ofString "q") .one
              (.op .and [.op .add [.var .local (ofString "p"), .op .add [.var .local (ofString "n"), .const 7]],
                .op .sub [.const 0, .const 8]])
              (.seq
                (.ite (.cmp .lower (.const Wave8Contracts.M26.cMax) (.var .local (ofString "q")))
                  (.call (some (none, none)) (ofString "trap_with") [.const 1])
                  .skip)
                (.seq
                  (.assign .global (ofString "heap_ptr") (.var .local (ofString "q")))
                  (.return (.var .local (ofString "p"))))))) := rfl
    have htrap_exn : ∀ (u : PanSemStateFiniteExact 64 F), u.code = originalRuntimeCode →
        (evaluateHOLFiniteState u (.call (some (none, none)) (ofString "trap_with") [.const 1])).1 ≠
          some (.exception ex v) := by
      intro u hcu heq
      rw [evaluateHOLFiniteState_call] at heq
      have hargs : evalListHOLFinite u (h := fun a => Classical.propDecidable (u.memaddrs a)) [.const 1] =
          some [.val (.word 1)] := by rfl
      have hl := pan_one_word_lookup u.code.lookup (ofString "trap_with") (ofString "code")
        (sourceFnBody Guest.Software.guestFn_trap_with) 1 (by rw [hcu]; exact lookup_trap_with)
      rw [hargs] at heq; dsimp only at heq
      rw [hl] at heq; dsimp only at heq
      split at heq
      · simp at heq
      · have hout := evaluate_trap_with_body_outcomes
          (callEntryStateHOLFinite u (HolFiniteMapExact.empty.update (ofString "code", .val (.word 1))))
        rcases hrun : evaluateHOLFiniteState
            (callEntryStateHOLFinite u (HolFiniteMapExact.empty.update (ofString "code", .val (.word 1))))
            (sourceFnBody Guest.Software.guestFn_trap_with) with ⟨rt, ut⟩
        rw [hrun] at heq hout
        rcases rt with _ | rt
        · simp at heq
        · cases rt with
          | exception eid ev =>
            dsimp only at heq
            injection heq with heq'
            cases heq'
            exact hout.2.2 ex v hne rfl
          | returned rv => exact hout.2.1 rv rfl
          | _ => simp at heq
    rw [hbody, evaluateHOLFiniteState_dec_total] at hex
    dsimp only at hex
    split at hex
    · simp at hex
    · split at hex
      · rename_i pv _ _
        set s1 := setVarHOLFinite (ofString "p") pv st
        rw [evaluateHOLFiniteState_seq_line780] at hex
        rcases hi1 : evaluateHOLFiniteState s1
            (.ite (.cmp .lower (.op .sub [.const Wave8Contracts.M26.cMax, .var .local (ofString "p")])
                (.var .local (ofString "n")))
              (.call (some (none, none)) (ofString "trap_with") [.const 1]) .skip) with ⟨r1, m1⟩
        rw [hi1] at hex
        cases r1 with
        | some r1' =>
          dsimp only at hex
          subst hex
          rw [evaluateHOLFiniteState_ite] at hi1
          split at hi1
          · split at hi1
            · rw [evaluateHOLFiniteState_skip] at hi1; simp at hi1
            · exact htrap_exn s1 hc (congrArg Prod.fst hi1)
          · simp at hi1
        | none =>
          have hm1 : m1.code = originalRuntimeCode := by
            have := (PanRunBounded.evaluateHOLFiniteState_metadata s1 _).1
            rw [hi1] at this; exact this.trans hc
          dsimp only at hex
          rw [evaluateHOLFiniteState_dec_total] at hex
          dsimp only at hex
          split at hex
          · simp at hex
          · split at hex
            · rename_i qv _ _
              set s2 := setVarHOLFinite (ofString "q") qv m1
              rw [evaluateHOLFiniteState_seq_line780] at hex
              rcases hi2 : evaluateHOLFiniteState s2
                  (.ite (.cmp .lower (.const Wave8Contracts.M26.cMax) (.var .local (ofString "q")))
                    (.call (some (none, none)) (ofString "trap_with") [.const 1]) .skip) with ⟨r2, m2⟩
              rw [hi2] at hex
              cases r2 with
              | some r2' =>
                dsimp only at hex
                subst hex
                rw [evaluateHOLFiniteState_ite] at hi2
                split at hi2
                · split at hi2
                  · rw [evaluateHOLFiniteState_skip] at hi2; simp at hi2
                  · exact htrap_exn s2 hm1 (congrArg Prod.fst hi2)
                · simp at hi2
              | none =>
                dsimp only at hex
                rw [evaluateHOLFiniteState_seq_line780] at hex
                rcases ha : evaluateHOLFiniteState m2 (.assign .global (ofString "heap_ptr") (.var .local (ofString "q"))) with ⟨ra, ma⟩
                rw [ha] at hex
                cases ra with
                | some _ =>
                  rw [evaluateHOLFiniteState_assign] at ha
                  split at ha
                  · rw [ha] at hex; simp at hex
                  · split at ha <;> (rw [ha] at hex; simp at hex)
                | none =>
                  dsimp only at hex
                  rw [evaluateHOLFiniteState_return] at hex
                  split at hex
                  · simp at hex
                  · split at hex <;> simp at hex
            · simp at hex
      · simp at hex

theorem NoExn.store_seq {d e : ExpHOL 64} {b : ProgHOL 64} (hb : NoExn b) :
    NoExn (.seq (.store d e) b) := by
  refine NoExn.seq ?_ hb
  intro F s _ hr
  rw [evaluateHOLFiniteState_store] at hr
  revert hr
  split
  · split
    · split
      · intro h; exact absurd h not_resumes_none
      · intro h; exact absurd h not_resumes_error
    · intro h; exact absurd h not_resumes_error
  · intro h; exact absurd h not_resumes_error

theorem NoExn.decCall_alloc (x : MlS) (arg : ExpHOL 64) {cont : ProgHOL 64}
    (hcont : NoExn cont) : NoExn (.decCall x .one (ofString "alloc") [arg] cont) := by
  intro F s hc hr
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hr ⊢
  revert hr
  split
  · intro h; exact absurd h not_resumes_error
  · rename_i values hargs
    split
    · intro h; exact absurd h not_resumes_error
    · rename_i body' callee ret hl
      have hsame := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "alloc") _ _ body'
        _ ret values callee (by rw [hc]; exact lookup_alloc) hl
      subst hsame
      split
      · intro h; exact absurd h not_resumes_timeout
      · dsimp only
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
            (sourceFnBody Guest.Software.guestFn_alloc) with ⟨r, cpost⟩
        rcases r with _ | r
        · intro h; exact absurd h not_resumes_error
        · cases r with
          | returned rv =>
            dsimp only
            split
            · intro hcont_r
              have hc_next : (setVarHOLFinite x rv { cpost with locals := s.locals }).code = originalRuntimeCode := by
                have hm := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee)
                  (sourceFnBody Guest.Software.guestFn_alloc)).1
                rw [hrun] at hm
                exact hm.trans hc
              exact hcont _ hc_next hcont_r
            · intro h; exact absurd h not_resumes_error
          | exception eid ev =>
            intro hres
            exfalso
            have hex := alloc_body_noExn (callEntryStateHOLFinite s callee) hc (by rw [hrun]; exact hres)
            rw [hrun] at hex
            rcases hex with ⟨_, h⟩
            cases h
          | _ =>
            intro h
            rcases h with ⟨_, hv⟩ | ⟨_, _, hv, _⟩ <;> cases hv

theorem nodeSize_bounds (k : Nat) : 32 ≤ nodeSize k ∧ nodeSize k ≤ 176 := by
  unfold nodeSize
  split_ifs <;> omega

theorem byteAlign_bounds (a : Nat) (ha : a < 2 ^ 64) :
    (panByteAlignHOL (BitVec.ofNat 64 a)).toNat ≤ a ∧
      a < (panByteAlignHOL (BitVec.ofNat 64 a)).toNat + 8 := by
  have h8 : 2 ^ Nat.log2 (64 / 8) = 8 := by decide
  simp only [panByteAlignHOL, h8, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]
  rw [Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_mul_le_self a 8) ha)]
  omega

theorem rootIn_cons_of_mem {x : Nat} {Nd : List Nat} {r : Nat} (h : RootIn Nd r) :
    RootIn (x :: Nd) r := by
  rcases h with rfl | hm
  · exact Or.inl rfl
  · exact Or.inr (List.mem_cons_of_mem x hm)

/-- Adding a newly allocated node `[hp, hp + sz)` in `[heap_ptr_s, heap_ptr_post)` preserves
every existing node in `Nd` and extends `NodeHeap` to `hp :: Nd`. -/
theorem nodeHeap_cons_fresh {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (hp sz : Nat)
    (hAR_s : ArenaReady s) (hAR_p : ArenaReady post)
    (hbe : post.be = s.be)
    (hAG : AllocatorGrows s post)
    (hhp_in : Inside (hp, sz) (globN s "heap_ptr") (globN post "heap_ptr"))
    (hhp_al : hp % 8 = 0)
    (hsz_eq : sz = nodeSize (memW post hp))
    (hfr_fresh : ∀ a : BitVec 64, ¬ (hp ≤ a.toNat ∧ a.toNat < hp + sz) → post.memory a = s.memory a)
    (hk_le : memW post hp ≤ 3)
    (hbr : memW post hp = 3 → ∀ i, i < 16 → memW post (hp + 32 + 8 * i) = 0)
    (h16 : memW post (hp + 16) < 2 ^ 40)
    (hleaf : memW post hp = 1 → memW post (hp + 56) < 2 ^ 40)
    (hbrv : memW post hp = 3 → memW post (hp + 168) < 2 ^ 40)
    (Nd : List Nat) (hNd : NodeHeap s Nd)
    (hpath : (memW post hp = 1 ∨ memW post hp = 2) → KeyIn s Nd (memW post (hp + 32)) (memW post (hp + 40)))
    (hchild2 : memW post hp = 2 → RootIn Nd (memW post (hp + 48))) :
    NodeHeap post (hp :: Nd) ∧
    (∀ n ∈ Nd, n ∈ hp :: Nd) ∧
    (∀ n ∈ Nd, memW post n = memW s n) ∧
    (∀ n ∈ hp :: Nd, n ∈ Nd ∨ Inside (nodeIvl post n) (globN s "heap_ptr") (globN post "heap_ptr")) ∧
    FrameOutside s post
      ((Nd.map fun n => nodeIvl s n) ++
        [(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")])
      (globN s "heap_ptr", heapLimit - globN s "heap_ptr") := by
  have hlim : heapLimit < 2 ^ 64 := by decide
  have hlim_he : heapLimit ≤ heapEnd := by decide
  have hsep : heapLimit ≤ scratchStart := by decide
  have hA_s := hAR_s.2
  have hA_p := hAR_p.2
  have hsz_b := nodeSize_bounds (memW post hp)
  have hsz_pos : 32 ≤ sz ∧ sz ≤ 176 := by omega
  have hsz_al : sz % 8 = 0 := by
    rw [hsz_eq]; unfold nodeSize; split_ifs <;> decide
  have hhp_bounds : sourceBase ≤ hp ∧ hp + sz ≤ globN post "heap_ptr" ∧ globN post "heap_ptr" ≤ heapLimit := by
    dsimp only [Inside] at hhp_in
    exact ⟨Nat.le_trans hA_s.1 hhp_in.1, hhp_in.2, hA_p.2.1⟩
  have hmem_below : ∀ a : Nat, a < globN s "heap_ptr" →
      post.memory (BitVec.ofNat 64 a) = s.memory (BitVec.ofNat 64 a) := by
    intro a ha
    have halt : a < 2 ^ 64 := by have := hA_s.2.1; omega
    apply hfr_fresh
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt halt]
    have := hhp_in.1; dsimp only at this
    omega
  have hmemW_below : ∀ a : Nat, a < globN s "heap_ptr" → memW post a = memW s a := by
    intro a ha; unfold memW; rw [hmem_below a ha]
  have hn_below : ∀ n ∈ Nd, n + nodeSize (memW s n) ≤ globN s "heap_ptr" := by
    intro n hn
    have hprop := hNd.1 n hn
    have hal := hprop.2.1
    have hin := hprop.2.2.1
    have hsb := nodeSize_bounds (memW s n)
    dsimp only [nodeIvl, Inside] at hin
    rcases hal with hal_h | hal_s
    · exact hal_h.2
    · dsimp only [nodeIvl, Inside] at hal_s
      have := hA_s.2.2.1; have := hA_s.2.2.2.1
      omega
  have hkind_old : ∀ n ∈ Nd, memW post n = memW s n := by
    intro n hn
    have hb := hn_below n hn
    have hsb := nodeSize_bounds (memW s n)
    exact hmemW_below n (by omega)
  have hivl_old : ∀ n ∈ Nd, nodeIvl post n = nodeIvl s n := by
    intro n hn; simp only [nodeIvl, hkind_old n hn]
  have hivl_hp : nodeIvl post hp = (hp, sz) := by
    simp only [nodeIvl, ← hsz_eq]
  have hKey_lift : ∀ p len, KeyIn s Nd p len → KeyIn post (hp :: Nd) p len := by
    intro p len hK
    by_cases hlen0 : len = 0
    · exact Or.inl hlen0
    · rcases hK with rfl | ⟨hnib, hal, hin, hdis⟩
      · exact absurd rfl hlen0
      · have hp_below : p + len ≤ globN s "heap_ptr" := by
          rcases hal with hh | hs
          · exact hh.2
          · dsimp only [Inside] at hin hs
            have := hA_s.2.2.1; have := hA_s.2.2.2.1
            omega
        refine Or.inr ⟨?_, hAG.allocated hal, hin, ?_⟩
        · intro k hk
          have hpk_lt : p + k < 2 ^ 64 := by have := hA_s.2.1; omega
          have hcell := byteAlign_bounds (p + k) hpk_lt
          have hal_al : (panByteAlignHOL (BitVec.ofNat 64 (p + k))).toNat % 8 = 0 := by
            have h8 : 2 ^ Nat.log2 (64 / 8) = 8 := by decide
            simp only [panByteAlignHOL, h8, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpk_lt]
            rw [Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_mul_le_self (p + k) 8) hpk_lt)]
            omega
          have hcell_lt_hp : (panByteAlignHOL (BitVec.ofNat 64 (p + k))).toNat + 8 ≤ globN s "heap_ptr" := by
            have := hA_s.2.2.2.2.2.1
            omega
          have hm_eq : post.memory (panByteAlignHOL (BitVec.ofNat 64 (p + k))) =
              s.memory (panByteAlignHOL (BitVec.ofNat 64 (p + k))) := by
            apply hfr_fresh
            have := hhp_in.1; dsimp only at this
            omega
          unfold memB; rw [hm_eq, hbe]; exact hnib k hk
        · intro m hm
          simp only [List.mem_cons] at hm
          rcases hm with rfl | hm'
          · rw [hivl_hp]
            exact Or.inr (Or.inr (Or.inl (Nat.le_trans hp_below hhp_in.1)))
          · rw [hivl_old m hm']
            exact hdis m hm'
  refine ⟨?_, fun n hn => List.mem_cons_of_mem hp hn, hkind_old, ?_, ?_⟩
  · -- `NodeHeap post (hp :: Nd)`
    refine ⟨?_, ?_⟩
    · intro n hn
      simp only [List.mem_cons] at hn
      rcases hn with rfl | hn_old
      · -- New node
        rw [hivl_hp]
        refine ⟨hk_le, Or.inl ⟨hhp_bounds.1, hhp_bounds.2.1⟩,
          ⟨hhp_bounds.1, Nat.le_trans hhp_bounds.2.1 hhp_bounds.2.2⟩,
          Wave8Contracts.M26.wordsOK_of_guestInv post hAR_p.1 n sz hhp_al hsz_al hhp_bounds.1 (by omega),
          fun h2 => rootIn_cons_of_mem (hchild2 h2),
          fun h3 i hi => Or.inl (hbr h3 i hi),
          fun h12 => hKey_lift _ _ (hpath h12),
          h16, hleaf, hbrv⟩
      · -- Existing node `n ∈ Nd`
        have hp_n := hNd.1 n hn_old
        have hb := hn_below n hn_old
        have hsb := nodeSize_bounds (memW s n)
        have hoff_eq : ∀ off, off < nodeSize (memW s n) → memW post (n + off) = memW s (n + off) :=
          fun off hoff => hmemW_below (n + off) (by omega)
        rw [hkind_old n hn_old, hivl_old n hn_old]
        refine ⟨hp_n.1, hAG.allocated hp_n.2.1, hp_n.2.2.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rcases hp_n.2.2.2.1 with ⟨ha1, ha2, hw⟩
          refine ⟨ha1, ha2, fun k hk => ?_⟩
          obtain ⟨_, hdom, _⟩ := hw k hk
          have hdom' : post.memaddrs (BitVec.ofNat 64 ((nodeIvl s n).1 + 8 * k)) := by
            rw [hAR_p.1.memaddrs, ← hAR_s.1.memaddrs]; exact hdom
          cases hc : post.memory (BitVec.ofNat 64 ((nodeIvl s n).1 + 8 * k)) with
          | word cw => exact ⟨cw, hdom', hc⟩
        · intro hk2
          have hsz2 : nodeSize (memW s n) = 56 := by simp [nodeSize, hk2]
          rw [hoff_eq 48 (by omega)]
          exact rootIn_cons_of_mem (hp_n.2.2.2.2.1 hk2)
        · intro hk3 i hi
          have hsz3 : nodeSize (memW s n) = 176 := by simp [nodeSize, hk3]
          have heq_i : n + 32 + 8 * i = n + (32 + 8 * i) := by omega
          rw [heq_i, hoff_eq (32 + 8 * i) (by omega), ← heq_i]
          exact rootIn_cons_of_mem (hp_n.2.2.2.2.2.1 hk3 i hi)
        · intro hk12
          have hsz12 : 56 ≤ nodeSize (memW s n) := by
            rcases hk12 with hk1 | hk2 <;> simp [nodeSize, *]
          rw [hoff_eq 32 (by omega), hoff_eq 40 (by omega)]
          exact hKey_lift _ _ (hp_n.2.2.2.2.2.2.1 hk12)
        · rw [hoff_eq 16 (by omega)]
          exact hp_n.2.2.2.2.2.2.2.1
        · intro hk1
          have hsz1 : nodeSize (memW s n) = 64 := by simp [nodeSize, hk1]
          rw [hoff_eq 56 (by omega)]
          exact hp_n.2.2.2.2.2.2.2.2.1 hk1
        · intro hk3
          have hsz3 : nodeSize (memW s n) = 176 := by simp [nodeSize, hk3]
          rw [hoff_eq 168 (by omega)]
          exact hp_n.2.2.2.2.2.2.2.2.2 hk3
    · -- Pairwise disjointness on `hp :: Nd`
      intro n hn m hm hne
      simp only [List.mem_cons] at hn hm
      rcases hn with rfl | hn_old
      · rcases hm with rfl | hm_old
        · exact absurd rfl hne
        · rw [hivl_hp, hivl_old m hm_old]
          have hb := hn_below m hm_old
          exact Or.inr (Or.inr (Or.inr (Nat.le_trans hb hhp_in.1)))
      · rcases hm with rfl | hm_old
        · rw [hivl_old n hn_old, hivl_hp]
          have hb := hn_below n hn_old
          exact Or.inr (Or.inr (Or.inl (Nat.le_trans hb hhp_in.1)))
        · rw [hivl_old n hn_old, hivl_old m hm_old]
          exact hNd.2 n hn_old m hm_old hne
  · -- Freshness of `n ∈ hp :: Nd`
    intro n hn
    simp only [List.mem_cons] at hn
    rcases hn with rfl | hn_old
    · right; rw [hivl_hp]; exact hhp_in
    · exact Or.inl hn_old
  · -- `FrameOutside`
    intro a _ hfresh
    apply hfr_fresh
    intro hin
    apply hfresh
    dsimp only [CellHits]
    have := hhp_in.1; have := hhp_in.2; have := hA_p.2.1
    dsimp only at *
    omega

end InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_HtabUnionAndMptLeaves
