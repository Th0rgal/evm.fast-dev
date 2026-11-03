import InitECandidate.Solver.Wave8GuestInv.ContractParts.C00Defs
import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.HtabC00Ports.SupportBase
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.ro_htab_item
import InitECandidate.Solver.Wave8GuestInv.R13Shards.HtabSetSpec

/-! Standalone complete proof of `htab_union_into_spec` (`ContractParts/C00.lean:58`)
for `R16e-M4b-M1r2-HtabUnion`. -/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

namespace HtabUnionInto

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
  | _ :: rest, _ => by
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

theorem at_lookup {Pc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
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
    · rename_i body' callee ret hl
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
  simp only [ha] at hflow ⊢
  cases r with
  | none => exact Or.inl ⟨mid, rfl, hflow, rfl⟩
  | some _ => exact Or.inr ⟨by simp [ha], by simpa [ha] using hflow, rfl⟩

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
  have hx := at_lookup hset st hcode _ body' callee ret hl hE hnt
  rw [hrun] at hx
  have hx' : ExitR (locN (callEntryStateHOLFinite st callee) "t")
      (callEntryStateHOLFinite st callee) cpost := hx v rfl
  rw [htE] at hx'
  have hpost : post = { cpost with locals := st.locals } := congrArg Prod.snd heq
  have hxR : ExitR (locN st "dst") st post := by
    have h2 : ExitR (locN st "dst") { st with locals := callee, clock := st.clock - 1 }
        { cpost with locals := cpost.locals, clock := cpost.clock } := hx'
    rw [exitR_locals] at h2
    rw [hpost]
    show ExitR (locN st "dst") { st with locals := st.locals, clock := st.clock }
      { cpost with locals := st.locals, clock := cpost.clock }
    rw [exitR_locals]
    exact h2
  have hAR := hxR.1
  have hWF := hxR.2.1
  have hfoot := hxR.2.2.2.2.2.1
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
  have hitem := at_lookup hro (decClockHOLFinite x) hxcode values body' callee ret hl hceG hnt_item
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
  set iteProg : ProgHOL 64 := .ite cond
    (.call (some (none, none)) (ofString "htab_set") (.var .local (ofString "dst") :: setRest))
    .skip
  have h_ite_step : ∀ mid,
      Wave8M19.Htab.FlowR (evaluateHOLFiniteState s1 iteProg).1 →
      mid = (evaluateHOLFiniteState s1 iteProg).2 →
      mid.code = originalRuntimeCode ∧
      mid.locals = s1.locals ∧
      UnionArgWF mid ∧
      ExitR (locN s0 "dst") s0 mid := by
    intro mid hif hmid_eq
    rcases ite_flow_split s1 _ _ _ hif with ⟨hyf, hyeq⟩ | ⟨hnf, hneq⟩
    · dsimp only [iteProg] at hmid_eq
      rw [hyeq] at hmid_eq
      subst hmid_eq
      obtain ⟨hcd, hlc, hUp, hRp⟩ := call_htab_set_step hset s1 _ hs1_code hs1_U hyf
      have hdst1 : locN s1 "dst" = locN s0 "dst" := by simp only [locN, hs1_dst]
      rw [hdst1] at hRp
      exact ⟨hcd, hlc, hUp, hs1_R.trans hRp⟩
    · dsimp only [iteProg] at hmid_eq
      rw [hneq, evaluateHOLFiniteState_skip] at hmid_eq
      subst hmid_eq
      exact ⟨hs1_code, rfl, hs1_U, hs1_R⟩
  have hpost' : (evaluateHOLFiniteState (decClockHOLFinite x)
      (.decCall (ofString "s") (.comb [.one, .one, .one]) (ofString "htab_item") itemArgs
        (.seq iteProg (.assign .local (ofString "i") incExp)))).2 =
      { (evaluateHOLFiniteState s1 (.seq iteProg (.assign .local (ofString "i") incExp))).2 with
        locals := HolFiniteMapExact.resVarEq
          (evaluateHOLFiniteState s1 (.seq iteProg (.assign .local (ofString "i") incExp))).2.locals
          (ofString "s", x.locals.lookup (ofString "s")) } := by
    exact hpost
  rcases seq_flow_split s1 iteProg (.assign .local (ofString "i") incExp) hcont with
    ⟨mid, hmid_none, hbf, hseq_eq⟩ | ⟨_, hif, hseq_eq⟩
  · obtain ⟨hm_code, hm_loc, hm_U, hm_R⟩ :=
      h_ite_step mid (Or.inl (by rw [hmid_none])) (by rw [hmid_none])
    obtain ⟨iv, _, hasg_eq⟩ := assign_local_flow mid _ _ hbf
    let mid_i := setVarHOLFinite (ofString "i") iv mid
    let fin_L := HolFiniteMapExact.resVarEq mid_i.locals (ofString "s", x.locals.lookup (ofString "s"))
    have hfin_eq : (evaluateHOLFiniteState (decClockHOLFinite x)
        (.decCall (ofString "s") (.comb [.one, .one, .one]) (ofString "htab_item") itemArgs
          (.seq iteProg (.assign .local (ofString "i") incExp)))).2 =
        { mid with locals := fin_L } := by
      rw [hpost', hseq_eq, hasg_eq]
      rfl
    rw [hfin_eq]
    refine ⟨hm_code, ?_, ?_, ?_⟩
    · dsimp only [fin_L, mid_i]
      rw [PanRunBounded.resVarEq_lookup]
      simp [show ofString "dst" ≠ ofString "s" by decide, setVarHOLFinite,
        HolFiniteMapExact.lookup_update, FUPDATE, show ofString "i" ≠ ofString "dst" by decide,
        hm_loc, hs1_dst]
    · exact localsOnly_unionArgWF mid fin_L mid.clock (fun n hn => by
        simp at hn; subst hn
        dsimp only [fin_L, mid_i]
        rw [PanRunBounded.resVarEq_lookup]
        simp [show ofString "dst" ≠ ofString "s" by decide, setVarHOLFinite,
          HolFiniteMapExact.lookup_update, FUPDATE, show ofString "i" ≠ ofString "dst" by decide]) hm_U
    · have h2 : ExitR (locN s0 "dst") { s0 with locals := s0.locals, clock := s0.clock }
          { mid with locals := fin_L, clock := mid.clock } := by
        rw [exitR_locals]; exact hm_R
      exact h2
  · let mid := (evaluateHOLFiniteState s1 iteProg).2
    obtain ⟨hm_code, hm_loc, hm_U, hm_R⟩ := h_ite_step mid hif rfl
    let fin_L := HolFiniteMapExact.resVarEq mid.locals (ofString "s", x.locals.lookup (ofString "s"))
    have hfin_eq : (evaluateHOLFiniteState (decClockHOLFinite x)
        (.decCall (ofString "s") (.comb [.one, .one, .one]) (ofString "htab_item") itemArgs
          (.seq iteProg (.assign .local (ofString "i") incExp)))).2 =
        { mid with locals := fin_L } := by
      rw [hpost', hseq_eq]
    rw [hfin_eq]
    refine ⟨hm_code, ?_, ?_, ?_⟩
    · dsimp only [fin_L]
      rw [PanRunBounded.resVarEq_lookup]
      simp [show ofString "dst" ≠ ofString "s" by decide, hm_loc, hs1_dst]
    · exact localsOnly_unionArgWF mid fin_L mid.clock (fun n hn => by
        simp at hn; subst hn
        dsimp only [fin_L]
        rw [PanRunBounded.resVarEq_lookup]
        simp [show ofString "dst" ≠ ofString "s" by decide]) hm_U
    · have h2 : ExitR (locN s0 "dst") { s0 with locals := s0.locals, clock := s0.clock }
          { mid with locals := fin_L, clock := mid.clock } := by
        rw [exitR_locals]; exact hm_R
      exact h2

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

end HtabUnionInto

theorem htab_union_into_spec :
    FunSpec UnionArgWF (OnReturn UnionExit) (ofString "htab_union_into") :=
  HtabUnionInto.htab_union_into_spec_of R13SoloHtabSet.htab_set_spec_proof

end InitECandidate.Solver.Wave8GuestInv.R16Shards
