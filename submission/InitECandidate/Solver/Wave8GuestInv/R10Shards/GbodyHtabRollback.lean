import InitECandidate.Solver.Wave8GuestInv.ContractParts.C13
import InitECandidate.Solver.GuestTrapAndLookup

/-! Helper proofs for `gbody_htab_truncate` and `gbody_rollback_child_access` (`ContractParts/C14.lean`)
on R10 (`wave8/spec-r10`). Zero `sorry`, zero `native_decide`, standard axioms only. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyHtabRollback

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-! ## 1. Lookup and parameter extraction helpers -/

theorem lookup_htab_del :
    originalRuntimeCode.lookup (ofString "htab_del") =
      some ([(ofString "t", .one), (ofString "key", .one)],
        sourceFnBody Guest.Software.guestFn_htab_del, .one) :=
  lookup_of_guestAst_getElem 139 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_del) rfl

theorem lookup_htab_truncate :
    originalRuntimeCode.lookup (ofString "htab_truncate") =
      some ((sourceFunctionEntry Guest.Software.guestFn_htab_truncate).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 140 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_truncate) rfl

theorem lookup_htab_truncate_params :
    originalRuntimeCode.lookup (ofString "htab_truncate") =
      some ([(ofString "t", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_htab_truncate, .one) :=
  lookup_of_guestAst_getElem 140 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_truncate) rfl

theorem lookup_rollback_child_access :
    originalRuntimeCode.lookup (ofString "rollback_child_access") =
      some ((sourceFunctionEntry Guest.Software.guestFn_rollback_child_access).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 593 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rollback_child_access) rfl

private theorem foldl_lookup_preserved {α β : Type} [DecidableEq α]
    (pairs : List (α × β)) (init : α → Option β) (target : α)
    (hnot : ∀ q ∈ pairs, q.1 ≠ target) :
    List.foldl (fun map entry current => if current = entry.1 then some entry.2 else map current)
      init pairs target = init target := by
  induction pairs generalizing init with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    rw [ih _ (fun q hq => hnot q (List.mem_cons_of_mem _ hq))]
    have hne : target ≠ hd.1 := Ne.symm (hnot hd (by simp))
    simp [hne]

private theorem zip_fst_ne {α β γ : Type}
    (names : List (α × γ)) (vals : List β) (target : α)
    (hnot : ∀ q ∈ names, q.1 ≠ target) :
    ∀ p ∈ (names.map Prod.fst).zip vals, p.1 ≠ target := by
  induction names generalizing vals with
  | nil => intro p hp; simp at hp
  | cons hd tl ih =>
    cases vals with
    | nil => intro p hp; simp at hp
    | cons v vs =>
      intro p hp
      simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at hp
      rcases hp with rfl | hp'
      · exact hnot hd (by simp)
      · exact ih vs (fun q hq => hnot q (List.mem_cons_of_mem _ hq)) p hp'

theorem lookupCodeHOLFinite_param_at {width : Nat} [NeZero width]
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (fn : MlS) (pre : List (MlS × ShapeHOL)) (pk : MlS) (sk : ShapeHOL)
    (post : List (MlS × ShapeHOL)) (body : ProgHOL width) (rs : ShapeHOL)
    (hafter : ∀ q ∈ post, q.1 ≠ pk)
    (hlookup : code fn = some (pre ++ (pk, sk) :: post, body, rs))
    {vpre : List (ValueHOL width)} {vk : ValueHOL width} {vpost : List (ValueHOL width)}
    (hlen : vpre.length = pre.length)
    {foundBody : ProgHOL width} {locals : HolFiniteMapExact MlS (ValueHOL width)}
    {foundRs : ShapeHOL}
    (hfound : PanSemStateFiniteExact.lookupCodeHOLFinite code fn (vpre ++ vk :: vpost) =
      some (foundBody, locals, foundRs)) :
    foundBody = body ∧ locals.lookup pk = some vk := by
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
  split at hfound
  · cases hfound
  · rename_i exactBody exactLocals exactShape raw
    have heq := Option.some.inj hfound
    rcases Prod.mk.inj heq with ⟨rfl, hrest⟩
    rcases Prod.mk.inj hrest with ⟨rfl, _⟩
    unfold lookupCodeHOLExact at raw
    rw [hlookup] at raw
    dsimp only at raw
    split at raw
    · have rawEq := Option.some.inj raw
      rcases Prod.mk.inj rawEq with ⟨rfl, hrest2⟩
      rcases Prod.mk.inj hrest2 with ⟨rfl, _⟩
      refine ⟨rfl, ?_⟩
      dsimp only
      have hzip : (List.map Prod.fst (pre ++ (pk, sk) :: post)).zip (vpre ++ vk :: vpost) =
          (pre.map Prod.fst).zip vpre ++ (pk, vk) :: (post.map Prod.fst).zip vpost := by
        rw [List.map_append, List.map_cons, List.zip_append (by simp [hlen]), List.zip_cons_cons]
      rw [hzip, List.foldl_append, List.foldl_cons]
      rw [foldl_lookup_preserved ((post.map Prod.fst).zip vpost) _ pk
        (zip_fst_ne post vpost pk hafter)]
      simp
    · cases raw

theorem evalList_cons_inv {F : Type} (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64)
    (es : List (ExpHOL 64)) {values : List (ValueHOL 64)}
    (h : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) (e :: es) =
      some values) :
    ∃ v vs, values = v :: vs ∧
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e =
        some v := by
  rw [evalListHOLFinite_eq_toExact] at h
  simp only [evalListHOLExact] at h
  revert h
  rcases he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e
    with _ | v
  · simp
  · rcases hes : @evalListHOLExact 64 F _ s.toExact
        (fun a => Classical.propDecidable (s.memaddrs a)) es with _ | vs
    · simp
    · simp only [Option.some.injEq]
      intro h
      exact ⟨v, vs, h.symm, rfl⟩

theorem locals_ext {m1 m2 : HolFiniteMapExact MlS (ValueHOL 64)}
    (h : ∀ k, m1.lookup k = m2.lookup k) : m1 = m2 := by
  cases m1; cases m2
  simp only [HolFiniteMapExact.mk.injEq]
  exact funext h

/-! ## 2. `htab_truncate` body proof -/

theorem dec_flow {F : Type} (s : PanSemStateFiniteExact 64 F) (name : MlS) (shape : ShapeHOL)
    (init : ExpHOL 64) (body : ProgHOL 64)
    (hflow : (evaluateHOLFiniteState s (.dec name shape init body)).1 = none ∨
      (evaluateHOLFiniteState s (.dec name shape init body)).1 = some .continue) :
    ∃ v, (evaluateHOLFiniteState (setVarHOLFinite name v s) body).1 =
        (evaluateHOLFiniteState s (.dec name shape init body)).1 ∧
      evaluateHOLFiniteState s (.dec name shape init body) =
        ((evaluateHOLFiniteState (setVarHOLFinite name v s) body).1,
          { (evaluateHOLFiniteState (setVarHOLFinite name v s) body).2 with
            locals := HolFiniteMapExact.resVarEq
              (evaluateHOLFiniteState (setVarHOLFinite name v s) body).2.locals
              (name, s.locals.lookup name) }) := by
  rw [evaluateHOLFiniteState_dec_total] at hflow ⊢
  dsimp only at hflow ⊢
  revert hflow
  split
  · intro h; rcases h with h | h <;> cases h
  · rename_i v _
    split
    · intro _; exact ⟨v, rfl, rfl⟩
    · intro h; rcases h with h | h <;> cases h

theorem call0_flow {F : Type} (s : PanSemStateFiniteExact 64 F) (fname : MlS)
    (args : List (ExpHOL 64))
    (hflow : (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1 = none ∨
      (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1 = some .continue) :
    ∃ values body callee ret v cpost,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args =
        some values ∧
      lookupCodeHOLFinite s.code.lookup fname values = some (body, callee, ret) ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
        (some (.returned v), cpost) ∧
      evaluateHOLFiniteState s (.call (some (none, none)) fname args) =
        (none, { cpost with locals := s.locals }) := by
  rw [evaluateHOLFiniteState_call] at hflow ⊢
  revert hflow
  rcases hargs : evalListHOLFinite s
      (h := fun address => Classical.propDecidable (s.memaddrs address)) args with _ | values
  · intro h; rcases h with h | h <;> cases h
  · dsimp only
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body, callee, ret⟩
    · intro h; rcases h with h | h <;> cases h
    · dsimp only
      by_cases hz : s.clock = 0
      · simp only [hz, ↓reduceIte]; intro h; rcases h with h | h <;> cases h
      · simp only [hz, ↓reduceIte]
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with
          ⟨res, cpost⟩
        rcases res with _ | r
        · intro h; rcases h with h | h <;> cases h
        · cases r with
          | returned v =>
            try dsimp only
            split
            · intro _; exact ⟨values, body, callee, ret, v, cpost, rfl, hl, hrun, rfl⟩
            · intro h; rcases h with h | h <;> cases h
          | exception _ _ => (try dsimp only); intro h; rcases h with h | h <;> cases h
          | _ => (try dsimp only); intro h; rcases h with h | h <;> cases h

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
    post.locals = s0.locals ∧ HtabArgWF post ∧
      (hdr post (locN s0 "t") 3 + 1 = hdr s0 (locN s0 "t") 3 ∨
        post = { s0 with clock := post.clock }) := by
  intro post
  obtain ⟨v1, hr1, heq1⟩ := dec_flow s0 a .one e1 _ hflow
  set s1 := setVarHOLFinite a v1 s0 with hs1
  obtain ⟨v2, hr2, heq2⟩ := dec_flow s1 b .one e2 _ (by rw [hr1]; exact hflow)
  set s2 := setVarHOLFinite b v2 s1 with hs2
  obtain ⟨values, body', callee, ret, v, cpost, hargs, hl, hrun, heq3⟩ :=
    call0_flow s2 _ _ (by rw [hr2, hr1]; exact hflow)
  obtain ⟨tv, vs, rfl, htv⟩ := evalList_cons_inv s2 _ _ hargs
  have ht2 : s2.locals.lookup (ofString "t") = s0.locals.lookup (ofString "t") := by
    simp [hs2, hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm ha, Ne.symm hb]
  have hlook := lookup_htab_del
  have hcode2 : s2.code = originalRuntimeCode := hcode
  obtain ⟨_, hct⟩ := lookupCodeHOLFinite_param_at s2.code.lookup (ofString "htab_del") []
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
  obtain ⟨hAR, hWF, _, _, _, hfoot, _, _⟩ := hx'
  simp only [htE] at hWF hfoot
  refine ⟨by rw [hpost], ?_, ?_⟩
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

theorem htabArgWF_guestInv {F : Type} (s : PanSemStateFiniteExact 64 F) (h : HtabArgWF s) :
    GuestInv s := h.1.1

theorem callEntry_htab_del (rest : List (ExpHOL 64)) :
    CallEntryOn HtabArgWF HtabArgWF (ofString "htab_del") (.var .local (ofString "t") :: rest) := by
  intro F s values body callee ret hcode hs hargs hl
  obtain ⟨tv, vs, rfl, htv⟩ := evalList_cons_inv s _ _ hargs
  have hlook := lookup_htab_del
  obtain ⟨_, hct⟩ := lookupCodeHOLFinite_param_at s.code.lookup (ofString "htab_del") []
    (ofString "t") .one [(ofString "key", .one)] _ _ (by simp only [List.mem_singleton]; rintro _ rfl; decide)
    (by rw [hcode]; simpa using hlook) (vpre := []) (by simp) hl
  have hcalleeT : callee.lookup (ofString "t") = s.locals.lookup (ofString "t") := by
    rw [hct]
    simp only [evalHOLExact] at htv
    exact htv.symm
  exact localsOnly_htabArgWF s callee (s.clock - 1)
    (fun n hn => by simp at hn; subst hn; exact hcalleeT) hs

theorem gbody_htab_truncate_proof :
    (TerminatingFunBoundedOn GuestInv (ofString "htab_del") K.«htab_del») →
    (type_of% @htab_del_spec) →
    (type_of% @htab_del_progress_spec) →
    TerminatingFunBoundedOn HtabArgWF (ofString "htab_truncate") K.«htab_truncate» := by
  intro hfd_guest hdel hprog
  have hfd : TerminatingFunBoundedOn HtabArgWF (ofString "htab_del") K.«htab_del» :=
    hfd_guest.mono htabArgWF_guestInv
  refine ⟨_, _, _, lookup_htab_truncate, ?_⟩
  dsimp only [sourceFunctionEntry, Guest.Software.guestFn_htab_truncate,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine TerminatingProgBoundedOn.mono_bound (a := (2 ^ 64 + 1) * ((K.«htab_del» + 1) + 1) + 0) ?_ ?_
  · apply TerminatingProgBoundedOn.dec_onLocals localsOnly_htabArgWF _
      (by simp only [List.mem_singleton]; rintro _ rfl; decide) _ _
    refine TerminatingProgBoundedOn.seq_guestInv_after ?_ htabArgWF_guestInv
      (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _))
    apply TerminatingProgBoundedOn.while_rank_stationary (N := 2 ^ 64)
      (fun s => hdr s (locN s "t") 3) (fun s hs => LocalsOnly.decClock localsOnly_htabArgWF s hs)
    · apply TerminatingProgBoundedOn.dec_onLocals localsOnly_htabArgWF _
        (by simp only [List.mem_singleton]; rintro _ rfl; decide) _ _
      apply TerminatingProgBoundedOn.dec_onLocals localsOnly_htabArgWF _
        (by simp only [List.mem_singleton]; rintro _ rfl; decide) _ _
      exact TerminatingProgBoundedOn.call_on hfd _ _ (callEntry_htab_del _)
    · intro F s _ _ _
      exact Nat.le_of_lt (memW_lt s _)
    · intro F s hcode hs _ hflow
      have hs0 := LocalsOnly.decClock localsOnly_htabArgWF s hs
      obtain ⟨hloc, hP, hdec | hsame⟩ := trunc_iter hdel hprog (by decide) (by decide) _ _ _
        (decClockHOLFinite s) hcode hs0 hflow
      · refine ⟨hP, Or.inl ?_⟩
        have hl : ∀ u : PanSemStateFiniteExact 64 F, u.locals = (decClockHOLFinite s).locals →
            locN u "t" = locN (decClockHOLFinite s) "t" := fun u h => by simp only [locN, h]
        rw [hl _ hloc]
        change _ < hdr (decClockHOLFinite s) (locN (decClockHOLFinite s) "t") 3
        omega
      · refine ⟨hP, Or.inr (Or.inl ?_)⟩
        unfold SameHead
        rw [hsame]
        rfl
  · unfold K.«htab_truncate»
    omega

/-! ## 3. `rollback_child_access` helpers and body proof -/

theorem evalAt_loadL' {F : Type} (t : PanSemStateFiniteExact 64 F) (l : String) (k a : BitVec 64)
    (h : evalAt t (.load .one (.op .add [.var .local (ofString l), .const k])) =
      some (.val (.word a))) :
    a.toNat = memW t (locN t l + k.toNat) := by
  simp [evalAt, evalHOLExact, evalListHOLExact] at h
  rcases hl : t.locals.lookup (ofString l) with _ | v
  · simp [hl] at h
  · rcases v with x | fs | ⟨nm, fs⟩
    · cases x with
      | word x =>
        simp [hl, valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact] at h
        have hadd : BitVec.ofNat 64 (x.toNat + k.toNat) = x + k := by
          rw [BitVec.add_def]
        simp only [locN, memW, hl, hadd, h.2]
    · simp [hl, valueIsWord] at h
    · simp [hl, valueIsWord] at h

theorem evalAt_loadL {F : Type} (t : PanSemStateFiniteExact 64 F) (l : String) (k : BitVec 64)
    (v : ValueHOL 64)
    (h : evalAt t (.load .one (.op .add [.var .local (ofString l), .const k])) = some v) :
    ∃ a : BitVec 64, v = .val (.word a) ∧ a.toNat = memW t (locN t l + k.toNat) := by
  have hv : ∃ a : BitVec 64, v = .val (.word a) := by
    simp [evalAt, evalHOLExact, evalListHOLExact] at h
    rcases hl : t.locals.lookup (ofString l) with _ | w
    · simp [hl] at h
    · rcases w with x | fs | ⟨nm, fs⟩
      · cases x with
        | word x =>
          simp [hl, valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact] at h
          rcases hm : t.memory (x + k) with ⟨y⟩
          exact ⟨y, by rw [← h.2, hm]⟩
      · simp [hl, valueIsWord] at h
      · simp [hl, valueIsWord] at h
  obtain ⟨a, rfl⟩ := hv
  exact ⟨a, rfl, evalAt_loadL' t l k a h⟩

def IvlUnhit {F : Type} (s post : PanSemStateFiniteExact 64 F) (i : Ivl) : Prop :=
  ∀ a : BitVec 64, a.toNat % 8 = 0 → CellHits a.toNat i → post.memory a = s.memory a

theorem ivlUnhit_of_frameOutside {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {keep : List Ivl} {fresh i : Ivl}
    (hi1 : i.1 % 8 = 0) (hi2 : i.2 % 8 = 0)
    (hfr : FrameOutside s post keep fresh)
    (hk : ∀ j ∈ keep, j.1 % 8 = 0 ∧ j.2 % 8 = 0 ∧ Disj i j)
    (hf1 : fresh.1 % 8 = 0) (hf2 : fresh.2 % 8 = 0) (hf : Disj i fresh) :
    IvlUnhit s post i := by
  intro a ha8 hhit
  have hin : i.1 ≤ a.toNat ∧ a.toNat + 8 ≤ i.1 + i.2 := by
    unfold CellHits at hhit; omega
  apply hfr a
  · intro j hj hcj
    obtain ⟨hj1, hj2, hd⟩ := hk j hj
    rcases j with ⟨j1, j2⟩
    rcases i with ⟨i1, i2⟩
    obtain ⟨hin1, hin2⟩ := hin
    obtain ⟨hcj1, hcj2⟩ := hcj
    unfold Disj at hd
    dsimp only at hj1 hj2 hin1 hin2 hcj1 hcj2 hd
    rcases hd with h | h | h | h <;> omega
  · intro hcf
    rcases fresh with ⟨f1, f2⟩
    rcases i with ⟨i1, i2⟩
    obtain ⟨hin1, hin2⟩ := hin
    obtain ⟨hcf1, hcf2⟩ := hcf
    have hd := hf
    unfold Disj at hd
    dsimp only at hf1 hf2 hin1 hin2 hcf1 hcf2 hd
    rcases hd with h | h | h | h <;> omega

theorem memW_eq_of_ivlUnhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {i : Ivl} (hu : IvlUnhit s post i) {a : Nat}
    (ha8 : a % 8 = 0) (hhi : i.1 + i.2 ≤ 2 ^ 64) (hin : i.1 ≤ a ∧ a + 8 ≤ i.1 + i.2) :
    memW post a = memW s a := by
  have ha_lt : a < 2 ^ 64 := by omega
  have hmem := hu (BitVec.ofNat 64 a)
    (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]; exact ha8)
    (by unfold CellHits; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]; omega)
  unfold memW
  rw [hmem]

theorem wordsOK_transfer {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hgS : GuestInv s) (hgP : GuestInv post) {i : Ivl} (hw : WordsOK s i) :
    WordsOK post i := by
  refine ⟨hw.1, hw.2.1, fun k hk => ?_⟩
  obtain ⟨_, hdom, _⟩ := hw.2.2 k hk
  rcases hm : post.memory (BitVec.ofNat 64 (i.1 + 8 * k)) with ⟨w⟩
  refine ⟨w, ?_, hm⟩
  rw [hgP.memaddrs, ← hgS.memaddrs]
  exact hdom

theorem freeChain_congr_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {nodes ncap : Nat} (hn8 : nodes % 8 = 0) (hhi : nodes + (ncap + 1) * 32 ≤ 2 ^ 64)
    (hu : IvlUnhit s post (nodes, (ncap + 1) * 32)) :
    ∀ (Fr : List Nat) (head : Nat),
      (∀ f ∈ Fr, 1 ≤ f ∧ f ≤ ncap) →
      (FreeChain post nodes head Fr ↔ FreeChain s nodes head Fr)
  | [], _, _ => Iff.rfl
  | f :: rest, head, hFr => by
    have hf : 1 ≤ f ∧ f ≤ ncap := hFr f (by simp)
    have hnd : nodeF post nodes f 0 = nodeF s nodes f 0 := by
      unfold nodeF
      exact memW_eq_of_ivlUnhit hu (by omega) hhi ⟨by omega, by omega⟩
    simp only [FreeChain, hnd]
    exact and_congr Iff.rfl (freeChain_congr_unhit hn8 hhi hu rest _ (fun x hx => hFr x (by simp [hx])))

theorem htabFootprint_eq_of_hdr_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {t : Nat} (ht8 : t % 8 = 0) (hhdr_hi : t + 88 ≤ 2 ^ 64) (hu : IvlUnhit s post (t, 88)) :
    (∀ k, k < 11 → hdr post t k = hdr s t k) ∧ htabFootprint post t = htabFootprint s t := by
  have hhdr : ∀ k, k < 11 → hdr post t k = hdr s t k := fun k hk => by
    unfold hdr
    exact memW_eq_of_ivlUnhit hu (by omega) hhdr_hi ⟨by omega, by omega⟩
  refine ⟨hhdr, ?_⟩
  simp only [htabFootprint, hhdr 1 (by omega), hhdr 4 (by omega), hhdr 5 (by omega),
    hhdr 6 (by omega), hhdr 10 (by omega)]

private theorem nodup_length_le_of_le : ∀ (l : List Nat) (n : Nat),
    l.Nodup → (∀ x ∈ l, 1 ≤ x ∧ x ≤ n) → l.length ≤ n
  | l, 0, _, hb => by
    cases l with
    | nil => simp
    | cons a _ => have := hb a List.mem_cons_self; omega
  | l, n + 1, hnd, hb => by
    by_cases hm : n + 1 ∈ l
    · have hnd' : (l.erase (n + 1)).Nodup := hnd.erase _
      have hb' : ∀ x ∈ l.erase (n + 1), 1 ≤ x ∧ x ≤ n := by
        intro x hx
        have hne : x ≠ n + 1 := (hnd.mem_erase_iff.mp hx).1
        have hxl : x ∈ l := (hnd.mem_erase_iff.mp hx).2
        have := hb x hxl
        omega
      have ih := nodup_length_le_of_le (l.erase (n + 1)) n hnd' hb'
      have hlen : (l.erase (n + 1)).length = l.length - 1 := List.length_erase_of_mem hm
      have hpos : 0 < l.length := List.length_pos_of_mem hm
      omega
    · have hb' : ∀ x ∈ l, 1 ≤ x ∧ x ≤ n := by
        intro x hx
        have hne : x ≠ n + 1 := fun e => hm (e ▸ hx)
        have := hb x hx
        omega
      exact Nat.le_trans (nodup_length_le_of_le l n hnd hb') (Nat.le_succ n)

theorem htabWF_congr_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hgS : GuestInv s) (hgP : GuestInv post)
    {t : Nat} (hwf : HtabWF s t)
    (hu : ∀ i ∈ htabFootprint s t, IvlUnhit s post i) :
    HtabWF post t ∧ htabFootprint post t = htabFootprint s t := by
  have h264 : heapEnd ≤ 2 ^ 64 := by decide
  have hfp := hwf.1
  have ht_fp : (t, 88) ∈ htabFootprint s t := by simp [htabFootprint]
  have hnd_fp : (hdr s t 5, (hdr s t 10 + 1) * 32) ∈ htabFootprint s t := by simp [htabFootprint]
  have hord_fp : (hdr s t 6, (hdr s t 10 + 1) * 8) ∈ htabFootprint s t := by simp [htabFootprint]
  have ht8 : t % 8 = 0 := (hfp _ ht_fp).2.1
  have hnd8 : (hdr s t 5) % 8 = 0 := (hfp _ hnd_fp).2.1
  have hord8 : (hdr s t 6) % 8 = 0 := (hfp _ hord_fp).2.1
  have hhdr_hi : t + 88 ≤ 2 ^ 64 := by have := (hfp _ ht_fp).1.2; omega
  obtain ⟨hhdr, hfp_eq⟩ := htabFootprint_eq_of_hdr_unhit ht8 hhdr_hi (hu _ ht_fp)
  have hnd_hi : hdr s t 5 + (hdr s t 10 + 1) * 32 ≤ 2 ^ 64 := by have := (hfp _ hnd_fp).1.2; omega
  have hord_hi : hdr s t 6 + (hdr s t 10 + 1) * 8 ≤ 2 ^ 64 := by have := (hfp _ hord_fp).1.2; omega
  obtain ⟨hfp1, hfp2, hk1, hk2, hstr, hncap, hnext1, hnext2,
    L, I, Fr, hLlen, hnodup, hmem, hcntI, hL, hI, hr0, hrpos, hnroot, hpI, hdep, hfc⟩ := hwf
  have hlen_all : (L ++ I ++ Fr).length ≤ hdr s t 10 :=
    nodup_length_le_of_le _ _ hnodup (fun x hx => by have := (hmem x).1 hx; omega)
  have hlen_L : L.length ≤ hdr s t 10 := by
    simp only [List.length_append] at hlen_all; omega
  have hnd_eq : ∀ n, 1 ≤ n → n ≤ hdr s t 10 → ∀ off ∈ ([0, 8, 16, 24] : List Nat),
      nodeF post (hdr s t 5) n off = nodeF s (hdr s t 5) n off := by
    intro n hn1 hn2 off hoff
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
    unfold nodeF
    rcases hoff with rfl | rfl | rfl | rfl <;>
      exact memW_eq_of_ivlUnhit (hu _ hnd_fp) (by omega) hnd_hi ⟨by omega, by omega⟩
  have hLI_bound : ∀ n ∈ L ++ I, 1 ≤ n ∧ n ≤ hdr s t 10 := fun n hn => by
    have := (hmem n).1 (List.mem_append.2 (Or.inl hn)); omega
  refine ⟨?_, hfp_eq⟩
  unfold HtabWF
  rw [hfp_eq, hhdr 0 (by omega), hhdr 1 (by omega), hhdr 3 (by omega), hhdr 5 (by omega),
    hhdr 6 (by omega), hhdr 7 (by omega), hhdr 8 (by omega), hhdr 9 (by omega), hhdr 10 (by omega)]
  refine ⟨fun i hi => ⟨(hfp1 i hi).1, wordsOK_transfer hgS hgP (hfp1 i hi).2⟩,
    hfp2, hk1, hk2, hstr, hncap, hnext1, hnext2, L, I, Fr, hLlen, hnodup, hmem, hcntI,
    ?_, ?_, hr0, ?_, ?_, ?_, ?_, ?_⟩
  · intro idx hidx
    have hLi : L[idx] ∈ L ++ I := List.mem_append.2 (Or.inl (List.getElem_mem hidx))
    obtain ⟨hb1, hb2⟩ := hLI_bound L[idx] hLi
    have hord_eq : memW post (hdr s t 6 + 8 * idx) = memW s (hdr s t 6 + 8 * idx) :=
      memW_eq_of_ivlUnhit (hu _ hord_fp) (by omega) hord_hi ⟨by omega, by omega⟩
    rw [hord_eq, hnd_eq L[idx] hb1 hb2 24 (by simp), hnd_eq L[idx] hb1 hb2 16 (by simp)]
    exact hL idx hidx
  · intro n hn
    have hnLI : n ∈ L ++ I := List.mem_append.2 (Or.inr hn)
    obtain ⟨hb1, hb2⟩ := hLI_bound n hnLI
    obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6⟩ := hI n hn
    obtain ⟨h8_1, h8_2⟩ := hLI_bound _ hc2
    obtain ⟨h16_1, h16_2⟩ := hLI_bound _ hc3
    rw [hnd_eq n hb1 hb2 24 (by simp), hnd_eq n hb1 hb2 8 (by simp), hnd_eq n hb1 hb2 16 (by simp),
      hnd_eq _ h8_1 h8_2 0 (by simp), hnd_eq _ h16_1 h16_2 0 (by simp)]
    exact ⟨hc1, hc2, hc3, hc4, hc5, hc6⟩
  · intro hpos
    obtain ⟨hrm, hrp⟩ := hrpos hpos
    obtain ⟨hb1, hb2⟩ := hLI_bound _ hrm
    rw [hnd_eq _ hb1 hb2 0 (by simp)]
    exact ⟨hrm, hrp⟩
  · intro n hn
    have hnLI : n ∈ L ++ I := List.mem_append.2 (Or.inr hn)
    obtain ⟨hb1, hb2⟩ := hLI_bound n hnLI
    rw [hnd_eq n hb1 hb2 8 (by simp), hnd_eq n hb1 hb2 16 (by simp)]
    exact hnroot n hn
  · intro n hn hnr
    obtain ⟨hb1, hb2⟩ := hLI_bound n hn
    rw [hnd_eq n hb1 hb2 0 (by simp)]
    exact hpI n hn hnr
  · obtain ⟨dep, hdep⟩ := hdep
    refine ⟨dep, fun n hn hnr => ?_⟩
    obtain ⟨hb1, hb2⟩ := hLI_bound n hn
    have hp_mem : nodeF s (hdr s t 5) n 0 ∈ L ++ I := List.mem_append.2 (Or.inr (hpI n hn hnr))
    obtain ⟨hpb1, hpb2⟩ := hLI_bound _ hp_mem
    rw [hnd_eq n hb1 hb2 0 (by simp), hnd_eq _ hpb1 hpb2 8 (by simp), hnd_eq _ hpb1 hpb2 16 (by simp)]
    exact hdep n hn hnr
  · exact (freeChain_congr_unhit hnd8 hnd_hi (hu _ hnd_fp) Fr (hdr s t 9)
      (fun f hf => by have := (hmem f).1 (List.mem_append.2 (Or.inr hf)); omega)).2 hfc

/-- Disjointness of any `Allocated s` interval from fresh heap `(heap_ptr s, heap_ptr post - heap_ptr s)`. -/
theorem disj_allocated_fresh_heap {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hs : ArenaOK s) (hp : ArenaOK post)
    {i : Ivl} (hi : Allocated s i) :
    Disj i (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") := by
  rcases hi with hi | hi
  · exact Or.inr (Or.inr (Or.inl hi.2))
  · rcases hs with ⟨_, _, hframe, hgap, _, _, _, _⟩
    have hsep : heapLimit ≤ scratchStart := by decide
    have hhp : globN post "heap_ptr" ≤ heapLimit := hp.2.1
    have hsi : scratchStart ≤ i.1 := Nat.le_trans hframe (Nat.le_trans hgap hi.1)
    by_cases hle : globN s "heap_ptr" ≤ globN post "heap_ptr"
    · exact Or.inr (Or.inr (Or.inr (by
        have hsum : globN s "heap_ptr" + (globN post "heap_ptr" - globN s "heap_ptr") = globN post "heap_ptr" :=
          Nat.add_sub_of_le hle
        dsimp only
        omega)))
    · exact Or.inr (Or.inl (by
        have hzero : globN post "heap_ptr" - globN s "heap_ptr" = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_le hle)
        dsimp only
        exact hzero))

theorem allocated_mono_htabExit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hgrow : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hglob : ∀ k : MlS, k ∉ (["heap_ptr"] : List String).map ofString →
      s.globals.lookup k = post.globals.lookup k)
    {i : Ivl} (hi : Allocated s i) : Allocated post i := by
  have hscr : globN post "scratch_ptr" = globN s "scratch_ptr" := by
    have hg := hglob (ofString "scratch_ptr") (by decide)
    simp only [globN, hg]
  rcases hi with hi | hi
  · exact Or.inl ⟨hi.1, Nat.le_trans hi.2 hgrow⟩
  · exact Or.inr ⟨by rw [hscr]; exact hi.1, hi.2⟩

/-- Guard after the first `htab_truncate` call in `rollback_child_access`: `child+176` is ready. -/
def RollbackMid {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  ArenaReady s ∧
  HtabWF s (memW s (locN s "child" + 176)) ∧
  ∀ i ∈ htabFootprint s (memW s (locN s "child" + 176)), Allocated s i

theorem rollbackMid_guestInv {F : Type} (s : PanSemStateFiniteExact 64 F) (h : RollbackMid s) :
    GuestInv s := h.1.1

theorem callEntry_htab_truncate_168 (rest : List (ExpHOL 64)) :
    CallEntryOn RollbackReady HtabArgWF (ofString "htab_truncate")
      (.load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 168)]) :: rest) := by
  intro F s values body callee ret hcode hs hargs hl
  obtain ⟨tv, vs, rfl, htv⟩ := evalList_cons_inv s _ _ hargs
  obtain ⟨w, rfl, hw⟩ := evalAt_loadL s "child" (BitVec.ofNat 64 168) tv htv
  have hlook := lookup_htab_truncate_params
  obtain ⟨_, hct⟩ := lookupCodeHOLFinite_param_at s.code.lookup (ofString "htab_truncate") []
    (ofString "t") .one [(ofString "n", .one)] _ _ (by simp only [List.mem_singleton]; rintro _ rfl; decide)
    (by rw [hcode]; simpa using hlook) (vpre := []) (by simp) hl
  have hlocT : locN (callEntryStateHOLFinite s callee) "t" = memW s (locN s "child" + 168) := by
    have h1 : locN (callEntryStateHOLFinite s callee) "t" = w.toNat := by
      simp only [locN, callEntryStateHOLFinite, hct]
    have h2 : (BitVec.ofNat 64 168).toNat = 168 := by decide
    rw [h2] at hw
    exact h1.trans hw
  obtain ⟨hA, _, _, htabs, _⟩ := hs
  obtain ⟨hwf, hal⟩ := htabs 168 (by simp)
  refine ⟨(arenaReady_with_locals s callee (s.clock - 1)).2 hA, ?_, ?_⟩
  · rw [hlocT]
    exact (htabWF_with_locals s callee (s.clock - 1) _).2 hwf
  · rw [hlocT]
    intro i hi
    exact (hal i hi).1

theorem callEntry_htab_truncate_176 (rest : List (ExpHOL 64)) :
    CallEntryOn RollbackMid HtabArgWF (ofString "htab_truncate")
      (.load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 176)]) :: rest) := by
  intro F s values body callee ret hcode hs hargs hl
  obtain ⟨tv, vs, rfl, htv⟩ := evalList_cons_inv s _ _ hargs
  obtain ⟨w, rfl, hw⟩ := evalAt_loadL s "child" (BitVec.ofNat 64 176) tv htv
  have hlook := lookup_htab_truncate_params
  obtain ⟨_, hct⟩ := lookupCodeHOLFinite_param_at s.code.lookup (ofString "htab_truncate") []
    (ofString "t") .one [(ofString "n", .one)] _ _ (by simp only [List.mem_singleton]; rintro _ rfl; decide)
    (by rw [hcode]; simpa using hlook) (vpre := []) (by simp) hl
  have hlocT : locN (callEntryStateHOLFinite s callee) "t" = memW s (locN s "child" + 176) := by
    have h1 : locN (callEntryStateHOLFinite s callee) "t" = w.toNat := by
      simp only [locN, callEntryStateHOLFinite, hct]
    have h2 : (BitVec.ofNat 64 176).toNat = 176 := by decide
    rw [h2] at hw
    exact h1.trans hw
  obtain ⟨hA, hwf, hal⟩ := hs
  refine ⟨(arenaReady_with_locals s callee (s.clock - 1)).2 hA, ?_, ?_⟩
  · rw [hlocT]
    exact (htabWF_with_locals s callee (s.clock - 1) _).2 hwf
  · rw [hlocT]
    exact hal

theorem hoare_first_truncate
    (htrunc : FunSpec HtabArgWF (OnReturn HtabExit) (ofString "htab_truncate"))
    (rest : List (ExpHOL 64)) :
    Hoare RollbackReady
      (.call (some (none, none)) (ofString "htab_truncate")
        (.load .one (.op .add [.var .local (ofString "child"), .const (BitVec.ofNat 64 168)]) :: rest))
      (fun r t => r = none → RollbackMid t) := by
  refine ⟨fun {F} s hcode hP _ hr => ?_⟩
  have ⟨values, body', callee, ret', v, post, hargs, hl, hrun, heval⟩ :=
    call0_flow s _ _ (Or.inl hr)
  rw [heval]
  dsimp only
  have hPc := callEntry_htab_truncate_168 rest s values body' callee ret' hcode hP hargs hl
  have hQc := FunSpec.at_lookup htrunc s hcode values body' callee ret' hl hPc
    (by rw [hrun]; simp)
  rw [hrun] at hQc
  have hx := hQc v rfl
  obtain ⟨tv, vs, rfl, htv⟩ := evalList_cons_inv s _ _ hargs
  obtain ⟨w, rfl, hw⟩ := evalAt_loadL s "child" (BitVec.ofNat 64 168) tv htv
  have hlook := lookup_htab_truncate_params
  obtain ⟨_, hct⟩ := lookupCodeHOLFinite_param_at s.code.lookup (ofString "htab_truncate") []
    (ofString "t") .one [(ofString "n", .one)] _ _
    (by simp only [List.mem_singleton]; rintro _ rfl; decide)
    (by rw [hcode]; simpa using hlook) (vpre := []) (by simp) hl
  have hlocT : locN (callEntryStateHOLFinite s callee) "t" = memW s (locN s "child" + 168) := by
    have h1 : locN (callEntryStateHOLFinite s callee) "t" = w.toNat := by
      simp only [locN, callEntryStateHOLFinite, hct]
    have h2 : (BitVec.ofNat 64 168).toNat = 168 := by decide
    rw [h2] at hw
    exact h1.trans hw
  obtain ⟨hAR_post, hWF_168, _, _, hgrow, hfp_post, hfr, hglob⟩ := hx
  rw [hlocT] at hWF_168 hfp_post hfr
  have hfr_s : FrameOutside s post (htabFootprint s (memW s (locN s "child" + 168)))
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") := hfr
  have hgrow_s : globN s "heap_ptr" ≤ globN post "heap_ptr" := hgrow
  have hglob_s : ∀ k : MlS, k ∉ (["heap_ptr"] : List String).map ofString →
      s.globals.lookup k = post.globals.lookup k := hglob
  obtain ⟨hA_s, hal_c, hw_c, htabs, hsep⟩ := hP
  obtain ⟨hwf_168, hal_168⟩ := htabs 168 (by simp)
  obtain ⟨hwf_176, hal_176⟩ := htabs 176 (by simp)
  set c := locN s "child"
  set t1 := memW s (c + 168)
  set t2 := memW s (c + 176)
  have hc_hi : c + 280 ≤ 2 ^ 64 := by
    have h1 : heapLimit ≤ heapEnd := by decide
    have h2 : scratchEnd ≤ heapEnd := by decide
    have h3 : heapEnd ≤ 2 ^ 64 := by decide
    rcases hal_c with ⟨_, hi⟩ | ⟨_, hi⟩
    · have := hA_s.2.2.1; omega
    · have := hA_s.2.2.2.2.2.1; omega
  have hf1 : (globN s "heap_ptr") % 8 = 0 := hA_s.2.2.2.2.2.2.1
  have hf2 : (globN post "heap_ptr" - globN s "heap_ptr") % 8 = 0 := by
    have hp8 : (globN post "heap_ptr") % 8 = 0 := hAR_post.2.2.2.2.2.2.1
    omega
  have hu_c : IvlUnhit s post (c, 280) :=
    ivlUnhit_of_frameOutside hw_c.1 hw_c.2.1 hfr_s
      (fun j hj => ⟨(hwf_168.1 j hj).2.1, (hwf_168.1 j hj).2.2.1, (hal_168 j hj).2⟩)
      hf1 hf2 (disj_allocated_fresh_heap hA_s.2 hAR_post.2 hal_c)
  have hc8 : c % 8 = 0 := hw_c.1
  have hm176 : memW post (c + 176) = t2 :=
    memW_eq_of_ivlUnhit hu_c (by omega) hc_hi ⟨by omega, by omega⟩
  have hloc_c : locN { post with locals := s.locals } "child" = c := rfl
  have hmem_176 : memW { post with locals := s.locals } (c + 176) = memW post (c + 176) := rfl
  refine ⟨(arenaReady_with_locals post s.locals post.clock).2 hAR_post, ?_, ?_⟩
  · rw [hloc_c, hmem_176, hm176]
    rcases hsep with heq | hdisj
    · rw [← heq]
      exact (htabWF_with_locals post s.locals post.clock t1).2 hWF_168
    · have hu_t2 : ∀ i ∈ htabFootprint s t2, IvlUnhit s post i := by
        intro i hi
        have hi_ok := (hwf_176.1 i hi).2
        exact ivlUnhit_of_frameOutside hi_ok.1 hi_ok.2.1 hfr_s
          (fun j hj => ⟨(hwf_168.1 j hj).2.1, (hwf_168.1 j hj).2.2.1, (hdisj j hj i hi).flip⟩)
          hf1 hf2 (disj_allocated_fresh_heap hA_s.2 hAR_post.2 (hal_176 i hi).1)
      have ⟨hwf_post, _⟩ := htabWF_congr_unhit hA_s.1 hAR_post.1 hwf_176 hu_t2
      exact (htabWF_with_locals post s.locals post.clock t2).2 hwf_post
  · rw [hloc_c, hmem_176, hm176]
    change ∀ i ∈ htabFootprint post t2, Allocated post i
    rcases hsep with heq | hdisj
    · rw [← heq]
      exact fun i hi => (hfp_post i hi).1
    · have hu_t2 : ∀ i ∈ htabFootprint s t2, IvlUnhit s post i := by
        intro i hi
        have hi_ok := (hwf_176.1 i hi).2
        exact ivlUnhit_of_frameOutside hi_ok.1 hi_ok.2.1 hfr_s
          (fun j hj => ⟨(hwf_168.1 j hj).2.1, (hwf_168.1 j hj).2.2.1, (hdisj j hj i hi).flip⟩)
          hf1 hf2 (disj_allocated_fresh_heap hA_s.2 hAR_post.2 (hal_176 i hi).1)
      have ⟨_, hfp_eq⟩ := htabWF_congr_unhit hA_s.1 hAR_post.1 hwf_176 hu_t2
      rw [hfp_eq]
      intro i hi
      exact allocated_mono_htabExit hgrow_s hglob_s (hal_176 i hi).1

theorem seq_hoare_change
    {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {first second : ProgHOL 64} {a b : Nat}
    (h1 : TerminatingProgBoundedOn P first a) (hp : Hoare P first (fun r t => r = none → Q t))
    (h2 : TerminatingProgBoundedOn Q second b) :
    TerminatingProgBoundedOn P (.seq first second) (a + b) := by
  intro F state hcode hP
  have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata state first
  unfold TerminatingRunBounded
  dsimp only
  intro hnt
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rcases hr1 : evaluateHOLFiniteState state first with ⟨r1, mid⟩
  have hmid := hp.run state hcode hP
  simp only [hr1] at hmeta hnt hmid ⊢
  cases r1 with
  | none =>
    dsimp only at hnt ⊢
    have hnt1 : (evaluateHOLFiniteState state first).1 ≠ some .timeOut := by simp [hr1]
    obtain ⟨s1, k1⟩ := h1 state hcode hP hnt1
    rw [hr1] at s1 k1
    dsimp only at s1 k1
    obtain ⟨s2, k2⟩ := h2 mid (hmeta.1.trans hcode) (hmid (by simp) rfl) hnt
    exact ⟨by omega, by omega⟩
  | some r =>
    dsimp only at hnt ⊢
    have hnt1 : (evaluateHOLFiniteState state first).1 ≠ some .timeOut := by simpa [hr1] using hnt
    obtain ⟨s1, k1⟩ := h1 state hcode hP hnt1
    rw [hr1] at s1 k1
    dsimp only at s1 k1
    exact ⟨by omega, k1⟩

theorem gbody_rollback_child_access_proof :
    (TerminatingFunBoundedOn HtabArgWF (ofString "htab_truncate") K.«htab_truncate») →
    (type_of% @htab_truncate_spec) →
    TerminatingFunBoundedOn RollbackReady (ofString "rollback_child_access") K.«rollback_child_access» := by
  intro hft htrunc
  refine ⟨_, _, _, lookup_rollback_child_access, ?_⟩
  dsimp only [sourceFunctionEntry, Guest.Software.guestFn_rollback_child_access,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine TerminatingProgBoundedOn.mono_bound
    (seq_hoare_change
      (TerminatingProgBoundedOn.call_on hft _ _ (callEntry_htab_truncate_168 _))
      (hoare_first_truncate htrunc _)
      (TerminatingProgBoundedOn.seq_guestInv_after
        (TerminatingProgBoundedOn.call_on hft _ _ (callEntry_htab_truncate_176 _))
        rollbackMid_guestInv
        (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))) ?_
  unfold K.«rollback_child_access»
  omega

end InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyHtabRollback
