import InitECandidate.Solver.Wave8GuestInv.HtabC00Ports.DelSpecs

/-! `htab_truncate_spec`: proved unconditionally over R11 `Wave8GuestInv` from the verified
`htab_del_spec` and `htab_del_progress_spec`. -/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.HtabC00Ports

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-! ## `ExitR` (R11 `HtabExit` for an explicit table address `t`) -/

def ExitR {F : Type} (t : Nat) (s post : PanSemStateFiniteExact 64 F) : Prop :=
  let fresh : Ivl := (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr")
  ArenaReady post ∧ HtabWF post t ∧
  hdr post t 0 = hdr s t 0 ∧ hdr post t 1 = hdr s t 1 ∧
  globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
  (∀ i ∈ htabFootprint post t, Allocated post i ∧
    ((∃ j ∈ htabFootprint s t, Inside i j.1 (j.1 + j.2)) ∨ Inside i fresh.1 (fresh.1 + fresh.2))) ∧
  FrameOutside s post (htabFootprint s t) fresh ∧
  (∀ k : MlS, k ∉ (["heap_ptr"] : List String).map ofString → s.globals.lookup k = post.globals.lookup k)

theorem htabExit_iff {F : Type} (s post : PanSemStateFiniteExact 64 F) :
    HtabExit s post ↔ ExitR (locN s "t") s post := Iff.rfl

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

theorem locN_congr {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (n : String)
    (h : locals.lookup (ofString n) = s.locals.lookup (ofString n)) :
    locN { s with locals := locals, clock := k } n = locN s n := by
  simp only [locN, h]

theorem localsOnly_htabArgWF : LocalsOnly ["t"] HtabArgWF := by
  intro F s locals k hl hP
  have ht := locN_congr s locals k "t" (hl "t" (by simp))
  simp only [HtabArgWF, htabWF_with_locals, arenaReady_with_locals] at hP ⊢
  rw [ht]
  exact hP

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

theorem lookup_htab_del :
    originalRuntimeCode.lookup (ofString "htab_del") =
      some ([(ofString "t", .one), (ofString "key", .one)],
        sourceFnBody Guest.Software.guestFn_htab_del, .one) :=
  lookup_of_guestAst_getElem 139 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_del) rfl

theorem lookup_htab_truncate :
    originalRuntimeCode.lookup (ofString "htab_truncate") =
      some ([(ofString "t", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_htab_truncate, .one) :=
  lookup_of_guestAst_getElem 140 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_truncate) rfl

theorem locals_ext {m1 m2 : HolFiniteMapExact MlS (ValueHOL 64)}
    (h : ∀ k, m1.lookup k = m2.lookup k) : m1 = m2 := by
  cases m1; cases m2
  simp only [HolFiniteMapExact.mk.injEq]
  exact funext h

/-- A flowing run of `dec a (dec b (htab_del(t, …)))` from an `HtabArgWF` state `s0`. -/
theorem trunc_iter
    (hdel : FunSpec HtabArgWF (OnReturn HtabExit) (ofString "htab_del"))
    (hprog : FunSpec HtabArgWF (OnReturn HtabDelProgress) (ofString "htab_del"))
    {a b : MlS} (ha : ofString "t" ≠ a) (hb : ofString "t" ≠ b) (e1 e2 : ExpHOL 64)
    (rest : List (ExpHOL 64)) {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (hcode : s0.code = originalRuntimeCode) (hs : HtabArgWF s0)
    (hflow : (evaluateHOLFiniteState s0 (.dec a .one e1 (.dec b .one e2
        (.call (some (none, none)) (ofString "htab_del") (.var .local (ofString "t") :: rest))))).1
        = none ∨
      (evaluateHOLFiniteState s0 (.dec a .one e1 (.dec b .one e2
        (.call (some (none, none)) (ofString "htab_del") (.var .local (ofString "t") :: rest))))).1
        = some .continue) :
    let post := (evaluateHOLFiniteState s0 (.dec a .one e1 (.dec b .one e2
        (.call (some (none, none)) (ofString "htab_del") (.var .local (ofString "t") :: rest))))).2
    post.locals = s0.locals ∧ HtabArgWF post ∧ ExitR (locN s0 "t") s0 post ∧
      (hdr post (locN s0 "t") 3 + 1 = hdr s0 (locN s0 "t") 3 ∨
        post = { s0 with clock := post.clock }) := by
  intro post
  obtain ⟨v1, hr1, heq1⟩ := Wave8M19.Htab.dec_flow s0 a .one e1 _ hflow
  set s1 := setVarHOLFinite a v1 s0 with hs1
  obtain ⟨v2, hr2, heq2⟩ := Wave8M19.Htab.dec_flow s1 b .one e2 _ (by rw [hr1]; exact hflow)
  set s2 := setVarHOLFinite b v2 s1 with hs2
  obtain ⟨values, body', callee, ret, v, cpost, hargs, hl, hrun, heq3⟩ :=
    Wave8M19.Htab.call0_flow s2 _ _ (by rw [hr2, hr1]; exact hflow)
  obtain ⟨tv, vs, rfl, htv⟩ := Wave8M19.Htab.evalList_cons_inv s2 _ _ hargs
  have ht2 : s2.locals.lookup (ofString "t") = s0.locals.lookup (ofString "t") := by
    simp [hs2, hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm ha, Ne.symm hb]
  have hlook := lookup_htab_del
  have hcode2 : s2.code = originalRuntimeCode := hcode
  obtain ⟨_, hct⟩ := Wave8M19.Htab.lookupCodeHOLFinite_param_at s2.code.lookup (ofString "htab_del") []
    (ofString "t") .one [(ofString "key", .one)] _ _ (by simp only [List.mem_singleton]; rintro _ rfl; decide)
    (by rw [hcode2]; simpa using hlook) (vpre := []) (by simp) hl
  have hcalleeT : callee.lookup (ofString "t") = s0.locals.lookup (ofString "t") := by
    rw [hct, ← ht2]
    simp only [evalHOLExact] at htv
    exact htv.symm
  have hs2P : HtabArgWF s2 := by
    have nt : ∀ n ∈ ["t"], ofString n ≠ a := by simp [ha]
    have nt' : ∀ n ∈ ["t"], ofString n ≠ b := by simp [hb]
    exact LocalsOnly.setVar localsOnly_htabArgWF nt' v2 _
      (LocalsOnly.setVar localsOnly_htabArgWF nt v1 _ hs)
  have hE : HtabArgWF (callEntryStateHOLFinite s2 callee) :=
    localsOnly_htabArgWF s2 callee (s2.clock - 1)
      (fun n hn => by simp at hn; subst hn; exact hcalleeT.trans ht2.symm) hs2P
  have hnt : (evaluateHOLFiniteState (callEntryStateHOLFinite s2 callee) body').1 ≠
      some .timeOut := by rw [hrun]; simp
  have hx := FunSpec.at_lookup hdel s2 hcode2 _ body' callee ret hl hE hnt
  have hp := FunSpec.at_lookup hprog s2 hcode2 _ body' callee ret hl hE hnt
  rw [hrun] at hx hp
  have hx' := hx v rfl
  have hp' := hp v rfl
  have hpost : post = { cpost with locals := (HolFiniteMapExact.resVarEq
      (HolFiniteMapExact.resVarEq s2.locals (b, s1.locals.lookup b))
      (a, s0.locals.lookup a)) } := by
    show (evaluateHOLFiniteState s0 _).2 = _
    rw [heq1]; dsimp only
    rw [heq2]; dsimp only
    rw [heq3]
  have hL : HolFiniteMapExact.resVarEq
      (HolFiniteMapExact.resVarEq s2.locals (b, s1.locals.lookup b))
      (a, s0.locals.lookup a) = s0.locals := by
    apply locals_ext
    intro k
    rw [PanRunBounded.resVarEq_lookup, PanRunBounded.resVarEq_lookup]
    by_cases hka : k = a
    · simp [hka]
    · by_cases hkb : k = b
      · subst hkb
        simp [hka, hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hka]
      · simp [hka, hkb, hs2, hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          Ne.symm hka, Ne.symm hkb]
  rw [hL] at hpost
  have htE : locN (callEntryStateHOLFinite s2 callee) "t" = locN s0 "t" := by
    simp only [locN, callEntryStateHOLFinite, hcalleeT]
  have hxR : ExitR (locN s0 "t") s0 post := by
    have h : ExitR (locN s0 "t") (callEntryStateHOLFinite s2 callee) cpost := by
      rw [← htE]; exact hx'
    have h2 : ExitR (locN s0 "t") { s0 with locals := callee, clock := s2.clock - 1 }
        { cpost with locals := cpost.locals, clock := cpost.clock } := h
    rw [exitR_locals] at h2
    have hpost' : post = { cpost with locals := s0.locals, clock := cpost.clock } := hpost
    rw [hpost']
    show ExitR (locN s0 "t") { s0 with locals := s0.locals, clock := s0.clock }
      { cpost with locals := s0.locals, clock := cpost.clock }
    rw [exitR_locals]
    exact h2
  obtain ⟨hAR, hWF, _, _, _, hfoot, _, _⟩ := hx'
  simp only [htE] at hWF hfoot
  refine ⟨by rw [hpost], ?_, hxR, ?_⟩
  · have hpost' : post = { cpost with locals := s0.locals, clock := cpost.clock } := hpost
    rw [hpost']
    refine ⟨(arenaReady_with_locals cpost _ _).2 hAR, ?_, ?_⟩
    · show HtabWF { cpost with locals := s0.locals, clock := cpost.clock } (locN s0 "t")
      exact (htabWF_with_locals cpost _ _ _).2 hWF
    · show ∀ i ∈ htabFootprint cpost (locN s0 "t"), Allocated cpost i
      intro i hi
      exact (hfoot i hi).1
  · rcases hp' with hdec | hsame
    · left
      simp only [htE] at hdec
      rw [hpost]
      exact hdec
    · right
      dsimp only at hsame
      rw [hpost, hsame]
      rfl

theorem while_dec2call_noRet {F : Type} (cond : ExpHOL 64) (a b f : MlS) (sa sb : ShapeHOL)
    (e1 e2 : ExpHOL 64) (args : List (ExpHOL 64)) (s : PanSemStateFiniteExact 64 F)
    (w : ValueHOL 64) :
    (evaluateHOLFiniteState s (.while cond
      (.dec a sa e1 (.dec b sb e2 (.call (some (none, none)) f args))))).1 ≠
      some (.returned w) :=
  Wave8M19.Htab.while_noRet _ _
    (fun s v => (Wave8M19.Htab.dec2call_res s a b f sa sb e1 e2 args).1.1 v) _ s le_rfl w

def TInv {F : Type} (s0 u : PanSemStateFiniteExact 64 F) : Prop :=
  u.code = originalRuntimeCode ∧ u.locals.lookup (ofString "t") = s0.locals.lookup (ofString "t") ∧
    HtabArgWF u ∧ ExitR (locN s0 "t") s0 u

theorem trunc_loop
    (hdel : FunSpec HtabArgWF (OnReturn HtabExit) (ofString "htab_del"))
    (hprog : FunSpec HtabArgWF (OnReturn HtabDelProgress) (ofString "htab_del")) {F : Type}
    (s0 : PanSemStateFiniteExact 64 F) {a b : MlS} (ha : ofString "t" ≠ a) (hb : ofString "t" ≠ b)
    (cond e1 e2 : ExpHOL 64) (rest : List (ExpHOL 64)) (s1 u : PanSemStateFiniteExact 64 F)
    (hI : TInv s0 s1)
    (hu : evaluateHOLFiniteState s1 (.while cond (.dec a .one e1 (.dec b .one e2
      (.call (some (none, none)) (ofString "htab_del") (.var .local (ofString "t") :: rest))))) =
      (none, u)) : TInv s0 u := by
  have := Wave8M19.Htab.while_inv (TInv s0) cond _ ?_ s1.clock s1 le_rfl hI (by rw [hu])
  · rw [hu] at this; exact this
  · intro x hx _ hflow
    obtain ⟨hxcode, hxt, hxP, hxR⟩ := hx
    have hres := Wave8M19.Htab.dec2call_res (decClockHOLFinite x) a b (ofString "htab_del")
      .one .one e1 e2 (.var .local (ofString "t") :: rest)
    have hflow' := hflow.elim Or.inl (fun h => h.elim Or.inr (fun hb => absurd hb hres.1.2))
    obtain ⟨hloc, hP', hR', _⟩ := trunc_iter hdel hprog ha hb _ _ _
      (decClockHOLFinite x) hxcode (LocalsOnly.decClock localsOnly_htabArgWF x hxP) hflow'
    have htn : locN (decClockHOLFinite x) "t" = locN s0 "t" := by
      simp only [locN, decClockHOLFinite, hxt]
    rw [htn] at hR'
    exact ⟨(PanRunBounded.evaluateHOLFiniteState_metadata _ _).1.trans hxcode,
      by rw [hloc]; exact hxt, hP', hxR.trans (exitR_decClock _ _ _ hR')⟩

theorem htab_truncate_spec_of
    (hdel : FunSpec HtabArgWF (OnReturn HtabExit) (ofString "htab_del"))
    (hprog : FunSpec HtabArgWF (OnReturn HtabDelProgress) (ofString "htab_del")) :
    FunSpec HtabArgWF (OnReturn HtabExit) (ofString "htab_truncate") := by
  refine ⟨_, _, _, lookup_htab_truncate, ?_⟩
  intro F s0 hcode hP _ _ v hv
  have hb : sourceFnBody Guest.Software.guestFn_htab_truncate =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_htab_truncate).body := rfl
  suffices key : Wave8M19.Htab.Ret s0 (sourceFnBody Guest.Software.guestFn_htab_truncate)
      (fun _ post => HtabExit s0 post) from key v hv
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_htab_truncate,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map]
  apply Wave8M19.Htab.Ret.dec
  intro sv _
  set s1 := setVarHOLFinite (ofString "stride") sv s0 with hs1
  have hI1 : TInv s0 s1 := by
    refine ⟨hcode, by simp [hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "stride" ≠ ofString "t" by decide],
      LocalsOnly.setVar localsOnly_htabArgWF (by simp only [List.mem_singleton]; rintro _ rfl; decide) sv s0 hP, ?_⟩
    have h0 : ExitR (locN s0 "t") s0 s0 := ExitR.refl _ s0 hP.1 hP.2.1 hP.2.2
    have h2 : ExitR (locN s0 "t") { s0 with locals := s0.locals, clock := s0.clock }
        { s0 with locals := s1.locals, clock := s0.clock } := by
      rw [exitR_locals]; exact h0
    exact h2
  apply Wave8M19.Htab.Ret.seq
  · intro w hw
    exfalso
    exact while_dec2call_noRet _ _ _ _ _ _ _ _ _ _ w hw
  · intro u hu
    apply Wave8M19.Htab.Ret.ret
    intro val _
    have hIu : TInv s0 u := trunc_loop hdel hprog s0 (by decide) (by decide) _ _ _ _ s1 u hI1 hu
    obtain ⟨_, _, _, hR⟩ := hIu
    show ExitR (locN s0 "t") s0 _
    have h2 : ExitR (locN s0 "t") { s0 with locals := s0.locals, clock := s0.clock }
        { u with locals := u.locals, clock := u.clock } := hR
    rw [← exitR_locals (L1 := s0.locals) (k1 := s0.clock) (L2 := HolFiniteMapExact.resVarEq
      (emptyLocalsHOLFinite u).locals (ofString "stride", s0.locals.lookup (ofString "stride")))
      (k2 := u.clock)] at h2
    exact h2

theorem htab_truncate_spec :
    FunSpec HtabArgWF (OnReturn HtabExit) (ofString "htab_truncate") :=
  htab_truncate_spec_of htab_del_spec htab_del_progress_spec

end InitECandidate.Solver.Wave8GuestInv.HtabC00Ports
