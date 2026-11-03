import InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptUnwindMemory

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody.Unwind
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open RunFramesRace (evalAt)

-- Parameter extraction follows the proved HTAB_DEL support lemma.
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


theorem evalAt_loadL' {F : Type} (t : PanSemStateFiniteExact 64 F) (g : String) (k a : BitVec 64)
    (h : evalAt t (.load .one (.op .add [.var .local (ofString g), .const k])) =
      some (.val (.word a))) :
    a.toNat = memW t (locN t g + k.toNat) := by
  simp [evalAt, evalHOLExact, evalListHOLExact] at h
  rcases hg : t.locals.lookup (ofString g) with _ | v
  · simp [hg] at h
  · rcases v with x | fs | ⟨nm, fs⟩
    · cases x with
      | word x =>
        simp [hg, valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact] at h
        have hadd : BitVec.ofNat 64 (x.toNat + k.toNat) = x + k := by
          rw [BitVec.add_def]
        simp only [locN, memW, hg, hadd, h.2]
    · simp [hg, valueIsWord] at h
    · simp [hg, valueIsWord] at h

/-- A one-word load from `local + k` that succeeds yields the word `memW t (locN t g + k)`. -/
theorem evalAt_loadL {F : Type} (t : PanSemStateFiniteExact 64 F) (g : String) (k : BitVec 64)
    (v : ValueHOL 64)
    (h : evalAt t (.load .one (.op .add [.var .local (ofString g), .const k])) = some v) :
    ∃ a : BitVec 64, v = .val (.word a) ∧ a.toNat = memW t (locN t g + k.toNat) := by
  have hv : ∃ a : BitVec 64, v = .val (.word a) := by
    simp [evalAt, evalHOLExact, evalListHOLExact] at h
    rcases hg : t.locals.lookup (ofString g) with _ | w
    · simp [hg] at h
    · rcases w with x | fs | ⟨nm, fs⟩
      · cases x with
        | word x =>
          simp [hg, valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact] at h
          rcases hm : t.memory (x + k) with ⟨y⟩
          exact ⟨y, by rw [← h.2, hm]⟩
      · simp [hg, valueIsWord] at h
      · simp [hg, valueIsWord] at h
  obtain ⟨a, rfl⟩ := hv
  exact ⟨a, rfl, evalAt_loadL' t g k a h⟩


theorem seq_none {F : Type} {s : PanSemStateFiniteExact 64 F} {a b : ProgHOL 64}
    (h : (evaluateHOLFiniteState s (.seq a b)).1 = none) :
    (evaluateHOLFiniteState s a).1 = none ∧
    evaluateHOLFiniteState s (.seq a b) = evaluateHOLFiniteState (evaluateHOLFiniteState s a).2 b := by
  rw [evaluateHOLFiniteState_seq_line780] at h ⊢
  cases he : evaluateHOLFiniteState s a with
  | mk r t =>
    rw [he] at h
    cases r with
    | none => exact ⟨rfl, rfl⟩
    | some r => cases h

theorem dec_none {F : Type} {s : PanSemStateFiniteExact 64 F} {name : MlS}
    {shape : ShapeHOL} {init : ExpHOL 64} {body : ProgHOL 64}
    (h : (evaluateHOLFiniteState s (.dec name shape init body)).1 = none) :
    ∃ v, evalAt s init = some v ∧
      (evaluateHOLFiniteState (setVarHOLFinite name v s) body).1 = none ∧
      (evaluateHOLFiniteState s (.dec name shape init body)).2 =
        { (evaluateHOLFiniteState (setVarHOLFinite name v s) body).2 with
          locals := HolFiniteMapExact.resVarEq
            (evaluateHOLFiniteState (setVarHOLFinite name v s) body).2.locals
            (name, s.locals.lookup name) } := by
  rw [evaluateHOLFiniteState_dec_total] at h ⊢
  dsimp only at h ⊢
  split at h
  · cases h
  · rename_i v hv
    split at h
    · rename_i hshape
      exact ⟨v, hv, h, by simp only [hshape, ↓reduceIte]⟩
    · cases h

theorem assign_none {F : Type} {s : PanSemStateFiniteExact 64 F} {name : MlS} {e : ExpHOL 64}
    (h : (evaluateHOLFiniteState s (.assign .local name e)).1 = none) :
    ∃ v, evalAt s e = some v ∧
      (evaluateHOLFiniteState s (.assign .local name e)).2 = setVarHOLFinite name v s := by
  rw [evaluateHOLFiniteState_assign] at h ⊢
  split at h
  · cases h
  · rename_i v hv
    split at h
    · rename_i hvalid
      exact ⟨v, hv, by simp only [hvalid, ↓reduceIte]; rfl⟩
    · cases h

theorem evalList_cons {F : Type} {s : PanSemStateFiniteExact 64 F} {e : ExpHOL 64}
    {es : List (ExpHOL 64)} {values : List (ValueHOL 64)}
    (h : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      (e :: es) = some values) :
    ∃ v vs, values = v :: vs ∧ evalAt s e = some v ∧
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) es = some vs := by
  rw [evalListHOLFinite_eq_toExact] at h ⊢
  simp only [evalAt]
  simp only [evalListHOLExact] at h
  cases he : @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a)) e with
  | none => rw [he] at h; cases h
  | some v =>
    rw [he] at h
    cases hes : @evalListHOLExact 64 F _ s.toExact
        (fun a => Classical.propDecidable (s.memaddrs a)) es with
    | none => rw [hes] at h; cases h
    | some vs =>
      rw [hes] at h
      exact ⟨v, vs, (Option.some.inj h).symm, rfl, rfl⟩

theorem call_none {F : Type} {s : PanSemStateFiniteExact 64 F} {fname dest : MlS}
    {args : List (ExpHOL 64)}
    (h : (evaluateHOLFiniteState s (.call (some (some (.local, dest), none)) fname args)).1 = none) :
    ∃ values body callee ret v post,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values ∧
      lookupCodeHOLFinite s.code.lookup fname values = some (body, callee, ret) ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post) ∧
      shapeEqHOL (shapeOfHOLExact v) ret = true ∧
      isValidValueHOLExact s.toExact .local dest v = true ∧
      (evaluateHOLFiniteState s (.call (some (some (.local, dest), none)) fname args)).2 =
        setVarHOLFinite dest v { post with locals := s.locals } := by
  rw [evaluateHOLFiniteState_call] at h ⊢
  cases hargs : evalListHOLFinite s
      (h := fun a => Classical.propDecidable (s.memaddrs a)) args with
  | none => rw [hargs] at h; cases h
  | some values =>
    rw [hargs] at h
    dsimp only at h ⊢
    cases hl : lookupCodeHOLFinite s.code.lookup fname values with
    | none => rw [hl] at h; cases h
    | some entry =>
      obtain ⟨body, callee, ret⟩ := entry
      rw [hl] at h
      dsimp only at h ⊢
      by_cases hz : s.clock = 0
      · simp only [hz, ↓reduceIte] at h; cases h
      · simp only [hz, ↓reduceIte] at h ⊢
        cases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with
        | mk r post =>
          rw [hrun] at h
          cases r with
          | none => cases h
          | some r =>
            cases r with
            | returned v =>
              dsimp only at h ⊢
              split at h
              · rename_i hshape
                split at h
                · rename_i hvalid
                  exact ⟨values, body, callee, ret, v, post, rfl, hl, hrun, hshape, hvalid,
                    by simp only [hshape, hvalid, ↓reduceIte]; rfl⟩
                · cases h
              · cases h
            | _ => cases h

theorem lookup_return_shape {F : Type} {s : PanSemStateFiniteExact 64 F}
    {fname : MlS} {params : List (MlS × ShapeHOL)} {b body : ProgHOL 64}
    {values : List (ValueHOL 64)} {callee : HolFiniteMapExact MlS (ValueHOL 64)} {r ret : ShapeHOL}
    (hl : s.code.lookup fname = some (params, b, r))
    (he : lookupCodeHOLFinite s.code.lookup fname values = some (body, callee, ret)) : ret = r := by
  have he := lookupCodeHOLFinite_eq_some _ _ _ _ _ _ he
  unfold lookupCodeHOLExact at he
  rw [hl] at he
  dsimp only at he
  split at he
  · simp only [Option.some.injEq, Prod.mk.injEq] at he
    exact he.2.2.symm
  · cases he

/-- A successful assignment of a one-word call result forces the caller's destination
to have been a word already. This also excludes aggregate stores on continuing iterations. -/
theorem valid_word_destination {F : Type} {s : PanSemStateFiniteExact 64 F} {dest : MlS}
    {v : ValueHOL 64} (hs : shapeEqHOL (shapeOfHOLExact v) .one = true)
    (hv : isValidValueHOLExact s.toExact .local dest v = true) :
    ∃ a b : BitVec 64, s.locals.lookup dest = some (.val (.word a)) ∧ v = .val (.word b) := by
  cases v with
  | val w =>
    cases w with
    | word b =>
      simp only [isValidValueHOLExact, lookupKvarHOLExact] at hv
      cases hl : s.locals.lookup dest with
      | none => simp [hl] at hv
      | some v =>
        cases v with
        | val w => cases w with | word a => exact ⟨a, b, rfl, rfl⟩
        | rStruct vs => simp [hl, shapeOfHOLExact, shapeEqHOL] at hv
        | nStruct n vs => simp [hl, shapeOfHOLExact, shapeEqHOL] at hv
  | rStruct vs => simp [shapeOfHOLExact, shapeEqHOL] at hs
  | nStruct n vs => simp [shapeOfHOLExact, shapeEqHOL] at hs

theorem node_call {names : List String}
    {req : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Nat → Prop}
    {fname : MlS} {args : List (ExpHOL 64)} (hf : NodeFn names req fname)
    {F : Type} {s : PanSemStateFiniteExact 64 F} {ns : List Nat}
    (hc : s.code = originalRuntimeCode) (ha : ArenaReady s) (hn : NodeHeap s ns)
    (hentry : ∀ values body callee ret,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values →
      lookupCodeHOLFinite s.code.lookup fname values = some (body, callee, ret) →
      (∀ n ∈ names, RootIn ns (locN (callEntryStateHOLFinite s callee) n)) ∧
        req (callEntryStateHOLFinite s callee) ns)
    (hflow : (evaluateHOLFiniteState s
      (.call (some (some (.local, ofString "res"), none)) fname args)).1 = none) :
    let t := (evaluateHOLFiniteState s
      (.call (some (some (.local, ofString "res"), none)) fname args)).2
    ∃ nt, Extension s t ns nt ∧ NodeHeap t nt ∧ RootIn nt (locN t "res") ∧
      locN t "top" = locN s "top" := by
  obtain ⟨values, body, callee, ret, v, post, hargs, hl, hr, _, _, hout⟩ := call_none hflow
  obtain ⟨hroots, hreq⟩ := hentry values body callee ret hargs hl
  have hen : NodeArgs names req (callEntryStateHOLFinite s callee) :=
    ⟨localsFree_arenaReady s callee (s.clock - 1) ha, ns,
      (nodeHeap_locals s callee (s.clock - 1) ns).2 hn, hroots, hreq⟩
  have hspec := FunSpec.at_lookup hf s hc values body callee ret hl hen (by rw [hr]; simp)
  rw [hr] at hspec
  obtain ⟨hready, hheap, hscratch, hall⟩ := hspec (Or.inl ⟨v, rfl⟩)
  obtain ⟨nt, hnt, hsub, hkind, hfresh, hframe, _, hret⟩ :=
    hall ns ((nodeHeap_locals s callee (s.clock - 1) ns).2 hn) hroots hreq
  obtain ⟨w, rfl, hw⟩ := hret v rfl
  have hmeta := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body).2.2.1
  rw [hr] at hmeta
  dsimp only
  rw [hout]
  refine ⟨nt, ?_, ?_, ?_, ?_⟩
  · exact
      { ready := localsFree_arenaReady post _ post.clock hready
        grows := ⟨hheap, hscratch⟩
        subset := hsub
        kinds := hkind
        fresh := hfresh
        frame := hframe
        endian := hmeta }
  · exact (nodeHeap_locals post _ post.clock nt).2 hnt
  · rw [RunFramesRace.locN_setVar_same]
    exact hw
  · exact RunFramesRace.locN_setVar_ne _ _ _ _ (by decide)

end InitECandidate.Solver.Wave8GuestInv.GuardedBody.Unwind
