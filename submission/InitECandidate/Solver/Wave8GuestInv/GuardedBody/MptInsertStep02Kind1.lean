import InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptCuts

/-! The leaf case stops descent: `go` stays zero after cache invalidation and
`_insert_into_leaf`. The bound covers the complete body syntax using only the
supplied callee bounds. The normal-flow proof follows the kind-1 branch, carries
the key guard through the exact cache effect, and preserves `ArenaReady` through
the final parent store and local assignments. -/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

private def leafReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ locN s "level" ≤ locN s "klen" ∧ ∃ Nd,
    NodeHeap s Nd ∧ NodeKind s Nd "node" 1 ∧
    KeyIn s Nd (locN s "key" + locN s "level") (locN s "klen" - locN s "level")

private def leafDone : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ locN s "go" = 0

-- Track fall-through states and rule out an early `continue` in a sequence.
private def fallPost (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop) :
    ∀ {F : Type}, Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop :=
  fun r t => (r = none → Q t) ∧ r ≠ some .continue

private theorem fall_other {Q} {F : Type} (r : Option (PanSemResultExact 64))
    (t : PanSemStateFiniteExact 64 F) (hn : r ≠ none) (hc : r ≠ some .continue) :
    fallPost Q r t := ⟨fun h => (hn h).elim, hc⟩

private theorem fall_seq {P R Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {a b : ProgHOL 64} (ha : Hoare P a (fallPost R)) (hb : Hoare R b (fallPost Q)) :
    Hoare P (.seq a b) (fallPost Q) :=
  Hoare.seq ⟨fun s hc hp hn =>
    let h := ha.run s hc hp hn
    ⟨h.1, fun hr => fall_other _ _ hr h.2⟩⟩ hb

private theorem fall_ite {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {e : ExpHOL 64} {a b : ProgHOL 64}
    (ha : Hoare (fun s => P s ∧ CondTrue e s) a (fallPost Q))
    (hb : Hoare (fun s => P s ∧ CondFalse e s) b (fallPost Q)) :
    Hoare P (.ite e a b) (fallPost Q) :=
  Hoare.ite ha hb (fun _ _ => fall_other _ _ (by simp) (by simp))

private theorem fall_skip {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} :
    Hoare P .skip (fallPost P) := Hoare.skip (fun _ hp => ⟨fun _ => hp, by simp⟩)

private theorem fall_assign {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {name : MlS} {e : ExpHOL 64}
    (h : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
      P s → evalAt s e = some v → Q (setVarHOLFinite name v s)) :
    Hoare P (.assign .local name e) (fallPost Q) :=
  Hoare.assign (fun s v hp hv => ⟨fun _ => h s v hp hv, by simp⟩)
    (fun _ _ => fall_other _ _ (by simp) (by simp))

private theorem fall_dec {P R Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {names : List String} {name : MlS} {shape : ShapeHOL} {e : ExpHOL 64} {body : ProgHOL 64}
    (hne : ∀ n ∈ names, ofString n ≠ name) (hq : LocalsOnly names Q)
    (hi : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
      P s → evalAt s e = some v → R (setVarHOLFinite name v s))
    (hb : Hoare R body (fallPost Q)) : Hoare P (.dec name shape e body) (fallPost Q) :=
  Hoare.dec hne hi hb
    (fun r t locals hl hp => ⟨fun hr => hq t locals t.clock hl (hp.1 hr), hp.2⟩)
    (fun _ _ => fall_other _ _ (by simp) (by simp))

private theorem done_locals : LocalsOnly ["go"] leafDone := by
  intro F s locals k hl hp
  exact ⟨(arenaReady_with_locals s locals k).2 hp.1,
    (locN_congr s locals k "go" (hl "go" (by simp))).trans hp.2⟩

private theorem ready_locals : LocalsOnly ["node", "key", "klen", "level"] leafReady := by
  intro F s locals k hl hp
  have he (n : String) (hn : n ∈ ["node", "key", "klen", "level"]) :=
    locN_congr s locals k n (hl n hn)
  obtain ⟨ha, hle, Nd, hn, hk, hkey⟩ := hp
  refine ⟨(arenaReady_with_locals s locals k).2 ha, ?_⟩
  rw [he "level" (by simp), he "klen" (by simp)]
  refine ⟨hle, Nd, hn, ?_, ?_⟩
  · change locN _ "node" ∈ Nd ∧ memW s (locN _ "node") = 1
    rw [he "node" (by simp)]
    exact hk
  · change KeyIn s Nd _ _
    rw [he "key" (by simp)]
    exact hkey

private theorem done_assign (n : String) (e : ExpHOL 64) (hn : ofString n ≠ ofString "go") :
    Hoare leafDone (.assign .local (ofString n) e) (fallPost leafDone) := by
  apply fall_assign
  intro F s v hp _
  apply done_locals s _ s.clock _ hp
  intro m hm
  have hm' : m = "go" := by simpa using hm
  subst m
  simp [HolFiniteMapExact.update, FUPDATE, hn]

private theorem done_store (a v : ExpHOL 64) :
    Hoare leafDone (.store a v) (fallPost leafDone) := by
  refine ⟨fun {F} s _ hp _ => ?_⟩
  rw [evaluateHOLFiniteState_store]
  split
  · split
    · split
      · exact ⟨fun _ => ⟨⟨guestInv_congr (s := s) rfl rfl rfl rfl hp.1.1, hp.1.2⟩,
          hp.2⟩, by simp⟩
      · exact fall_other _ _ (by simp) (by simp)
    · exact fall_other _ _ (by simp) (by simp)
  · exact fall_other _ _ (by simp) (by simp)

private theorem bounded_straight (p : ProgHOL 64) (hp : extStraightLine p = true) :
    TerminatingProgBoundedOn GuestInv p 0 :=
  fun s hc _ => TerminatingProgBounded.straight p hp s hc

attribute [local irreducible] TerminatingProgBoundedOn

-- The two declaration calls also charge their scoped continuations.
private def leafCost : ProgHOL 64 → Nat
  | .seq a b => leafCost a + leafCost b
  | .ite _ a b => max (leafCost a) (leafCost b)
  | .dec _ _ _ b => leafCost b
  | .call _ f _ => mptCharge f + 1
  | .decCall _ _ f _ b => mptCharge f + leafCost b + 1
  | _ => 0

private theorem charge_0 : mptCharge (ofString "_insert_into_leaf") = K.«_insert_into_leaf» := rfl
private theorem charge_1 : mptCharge (ofString "_split_extension") = K.«_split_extension» := rfl
private theorem charge_2 : mptCharge (ofString "common_prefix_length") = K.«common_prefix_length» := rfl
private theorem charge_3 : mptCharge (ofString "mpt_fail") = K.«mpt_fail» := rfl
private theorem charge_4 : mptCharge (ofString "node_invalidate") = K.«node_invalidate» := rfl
private theorem charge_5 : mptCharge (ofString "node_new_ext") = K.«node_new_ext» := rfl
private theorem charge_6 : mptCharge (ofString "node_new_leaf") = K.«node_new_leaf» := rfl

private theorem insert_bounded (h : MptInsertCallees) :
    TerminatingProgBoundedOn GuestInv mptInsertBody mptInsertCost := by
  have hb : TerminatingProgBoundedOn GuestInv mptInsertBody (leafCost mptInsertBody) := by
    simp only [mptInsertBody, mptWhileBody, mptLeft, mptInsertTail, mptDecBody,
      mptInsertCode, sourceFunctionEntry, Guest.Software.guestFn__mpt_insert_node,
      InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
      List.map_cons, List.map_nil, Option.map_some, Option.map_none, leafCost]
    simp only [charge_0, charge_1, charge_2, charge_3, charge_4, charge_5, charge_6]
    repeat' first
      | exact TerminatingProgBoundedOn.call_guestInv h.fb__insert_into_leaf _ _
      | exact TerminatingProgBoundedOn.call_guestInv h.fb__split_extension _ _
      | exact TerminatingProgBoundedOn.call_guestInv h.fb_common_prefix_length _ _
      | exact TerminatingProgBoundedOn.call_guestInv h.fb_mpt_fail _ _
      | exact TerminatingProgBoundedOn.call_guestInv h.fb_node_invalidate _ _
      | exact TerminatingProgBoundedOn.call_guestInv h.fb_node_new_ext _ _
      | exact TerminatingProgBoundedOn.call_guestInv h.fb_node_new_leaf _ _
      | exact bounded_straight _ rfl
      | refine TerminatingProgBoundedOn.seq_guestInv ?_ ?_
      | refine TerminatingProgBoundedOn.ite_on ?_ ?_
      | refine TerminatingProgBoundedOn.dec_on localsFree_guestInv _ _ _ ?_
      | refine TerminatingProgBoundedOn.decCall_guestInv h.fb_common_prefix_length _ _ _ ?_
      | refine TerminatingProgBoundedOn.decCall_guestInv h.fb__split_extension _ _ _ ?_
  exact TerminatingProgBoundedOn.mono_bound hb (by
    simp only [leafCost, mptInsertBody, mptWhileBody, mptLeft, mptInsertTail, mptDecBody,
      mptInsertCode, sourceFunctionEntry, Guest.Software.guestFn__mpt_insert_node,
      InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
      List.map_cons, List.map_nil, Option.map_some, Option.map_none,
      charge_0, charge_1, charge_2, charge_3, charge_4, charge_5, charge_6,
      mptInsertCost, Nat.add_zero, Nat.zero_add, Nat.max_self]
    simp only [Nat.zero_max, Nat.max_zero]
    apply le_of_eq
    ac_rfl)

private theorem nodeSize_pos (k : Nat) : 32 ≤ nodeSize k := by
  unfold nodeSize
  split <;> try omega
  split <;> try omega
  split <;> omega

-- Cache words lie inside the old node record, away from every live key byte.
private theorem invalidation_key {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Nd Nd' : List Nat} {nd p len : Nat}
    (hh : NodeHeap s Nd) (hnd : nd ∈ Nd)
    (he : post = { clearCache s nd with locals := post.locals, clock := post.clock })
    (hsub : ∀ n ∈ Nd', n ∈ Nd)
    (hk : ∀ n ∈ Nd, memW post n = memW s n)
    (hkey : KeyIn s Nd p len) : KeyIn post Nd' p len := by
  rcases hkey with hz | ⟨hnib, ha, hi, hd⟩
  · exact Or.inl hz
  right
  refine ⟨?_, ?_, hi, ?_⟩
  · intro k hlen
    have hlim : heapLimit < 2^64 := by decide
    have hpk : p + k < 2^64 := by obtain ⟨_, _⟩ := hi; omega
    have hni := (hh.1 nd hnd).2.2.1
    have hns := nodeSize_pos (memW s nd)
    have hn24 : nd + 24 < 2^64 := by
      dsimp only [Inside, nodeIvl] at hni
      omega
    have hal :
        (panByteAlignHOL (BitVec.ofNat 64 (p + k))).toNat ≤ p + k ∧
        p + k < (panByteAlignHOL (BitVec.ofNat 64 (p + k))).toNat + 8 := by
      have h8 : 2 ^ Nat.log2 (64 / 8) = 8 := by decide
      simp only [panByteAlignHOL, h8, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpk]
      have hfit : (p + k) / 8 * 8 < 2^64 := by omega
      rw [Nat.mod_eq_of_lt hfit]
      omega
    have hdis := hd nd hnd
    dsimp only [Disj, nodeIvl] at hdis
    have hmem : post.memory (panByteAlignHOL (BitVec.ofNat 64 (p + k))) =
        s.memory (panByteAlignHOL (BitVec.ofNat 64 (p + k))) := by
      rw [he]
      dsimp only [clearCache]
      apply if_neg
      intro hit
      rcases hit with hit | hit | hit
      all_goals
        have heq := congrArg BitVec.toNat hit
        simp only [BitVec.toNat_ofNat] at heq
        have h8 : nd + 8 < 2^64 := by omega
        have h16 : nd + 16 < 2^64 := by omega
        simp only [Nat.mod_eq_of_lt hn24, Nat.mod_eq_of_lt h8, Nat.mod_eq_of_lt h16] at heq
        omega
    have hb : post.be = s.be := by rw [he]; rfl
    simpa only [memB, hmem, hb] using hnib k hlen
  · have hg : post.globals = s.globals := by rw [he]; rfl
    simpa only [Allocated, Inside, globN, hg] using ha
  · intro n hn
    simpa only [nodeIvl, hk n (hsub n hn)] using hd n (hsub n hn)

private theorem fall_call {P Pc Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Qc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop} {fname : MlS} {args : List (ExpHOL 64)}
    (dest : Option MlS) (hf : FunSpec Pc Qc fname) (he : CallEntryOn P Pc fname args)
    (hr : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F)
      (values : List (ValueHOL 64)) (body : ProgHOL 64)
      (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
      (post : PanSemStateFiniteExact 64 F)
      (v : ValueHOL 64), s.code = originalRuntimeCode → P s →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values →
      lookupCodeHOLFinite s.code.lookup fname values = some (body, callee, ret) →
      Qc (callEntryStateHOLFinite s callee) (some (.returned v)) post →
      Q (match dest with
        | none => { post with locals := s.locals }
        | some n => setVarHOLFinite n v { post with locals := s.locals })) :
    Hoare P (.call (some (dest.map (fun n => (.local, n)), none)) fname args) (fallPost Q) := by
  refine ⟨fun {F} s hc hp hn => ?_⟩
  rw [evaluateHOLFiniteState_call] at hn ⊢
  rcases ha : evalListHOLFinite s
      (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
  · exact fall_other _ _ (by simp) (by simp)
  rw [ha] at hn
  dsimp only at hn ⊢
  rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨b, callee, ret⟩
  · exact fall_other _ _ (by simp) (by simp)
  rw [hl] at hn
  dsimp only at hn ⊢
  by_cases hz : s.clock = 0
  · exact fall_other _ _ (by simp [hz]) (by simp [hz])
  simp only [hz, ↓reduceIte] at hn ⊢
  rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) b with ⟨r, post⟩
  rw [hb] at hn
  try dsimp only at hn ⊢
  have hspec (hnt : r ≠ some .timeOut) : Qc (callEntryStateHOLFinite s callee) r post := by
    have hh := FunSpec.at_lookup hf s hc values b callee ret hl
      (he s values b callee ret hc hp ha hl) (by rw [hb]; exact hnt)
    simpa only [hb] using hh
  cases r with
  | none => exact fall_other _ _ (by simp) (by simp)
  | some r =>
    cases r with
    | returned v =>
      dsimp only
      split
      · cases dest with
        | none => exact ⟨fun _ => hr s values b callee ret post v hc hp ha hl (hspec (by simp)), by simp⟩
        | some n =>
          dsimp only [Option.map]
          split
          · exact ⟨fun _ => hr s values b callee ret post v hc hp ha hl (hspec (by simp)), by simp⟩
          · exact fall_other _ _ (by simp) (by simp)
      · exact fall_other _ _ (by simp) (by simp)
    | timeOut => exact fall_other _ _ (by simp) (by simp)
    | exception e v => exact fall_other _ _ (by cases dest <;> simp) (by cases dest <;> simp)
    | _ => exact fall_other _ _ (by simp) (by simp)

private theorem callee_map {F : Type} (s : PanSemStateFiniteExact 64 F)
    (fname : MlS) (params : List (MlS × ShapeHOL)) (body : ProgHOL 64) (ret : ShapeHOL)
    (values : List (ValueHOL 64)) (b : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (r : ShapeHOL)
    (hc : s.code.lookup fname = some (params, body, ret))
    (hl : lookupCodeHOLFinite s.code.lookup fname values = some (b, callee, r)) :
    callee.lookup = List.foldl
      (fun (m : MlS → Option (ValueHOL 64)) (e : MlS × ValueHOL 64) =>
        fun n => if n = e.1 then some e.2 else m n)
      (fun _ => none) ((params.map Prod.fst).zip values) := by
  have hh := lookupCodeHOLFinite_eq_some _ _ _ _ _ _ hl
  unfold lookupCodeHOLExact at hh
  rw [hc] at hh
  dsimp only at hh
  split at hh
  · exact (congrArg (fun e => e.2.1) (Option.some.inj hh)).symm
  · cases hh

private theorem lookup_invalidate : originalRuntimeCode.lookup (ofString "node_invalidate") =
    some ((sourceFunctionEntry Guest.Software.guestFn_node_invalidate).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 259 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_node_invalidate) rfl

private theorem invalidate_param {F : Type} (s : PanSemStateFiniteExact 64 F)
    (vs : List (ValueHOL 64)) (b : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (r : ShapeHOL)
    (hc : s.code = originalRuntimeCode)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "node")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "node_invalidate") vs = some (b, callee, r)) :
    callee.lookup (ofString "nd") = s.locals.lookup (ofString "node") := by
  have hm := callee_map s _ _ _ _ vs b callee r (by rw [hc]; exact lookup_invalidate) hl
  rw [evalListHOLFinite_eq_toExact] at ha
  simp only [evalListHOLExact, evalHOLExact] at ha
  rcases hn : s.locals.lookup (ofString "node") with _ | v
  · simp only [hn] at ha; cases ha
  · simp only [hn, Option.some.injEq] at ha
    subst vs
    rw [hm]
    rfl

private theorem specs_and {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Q R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop} {f : MlS}
    (hq : FunSpec P Q f) (hr : FunSpec P R f) :
    FunSpec P (fun s r t => Q s r t ∧ R s r t) f := by
  obtain ⟨p, b, r, hl, hq⟩ := hq
  obtain ⟨p', b', r', hl', hr⟩ := hr
  rw [hl] at hl'
  cases hl'
  exact ⟨p, b, r, hl, fun s hc hp hn => ⟨hq s hc hp hn, hr s hc hp hn⟩⟩

private def leafTagged : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => leafReady s ∧ locN s "go" = 0 ∧ locN s "k" = 1

private theorem invalidate_entry : CallEntryOn leafTagged
    (NodeArgs ["nd"] (fun _ _ => True)) (ofString "node_invalidate")
    [.var .local (ofString "node")] := by
  intro F s vs b callee r hc hp ha hl
  have hparam := invalidate_param s vs b callee r hc ha hl
  have hn : locN (callEntryStateHOLFinite s callee) "nd" = locN s "node" := by
    simp only [locN, callEntryStateHOLFinite, hparam]
  obtain ⟨har, hle, Nd, hheap, hkind, hkey⟩ := hp.1
  refine ⟨(arenaReady_with_locals s callee (s.clock-1)).2 har, Nd, hheap, ?_, trivial⟩
  intro n hm
  have hn' : n = "nd" := by simpa using hm
  subst n
  rw [hn]
  exact Or.inr hkind.1

-- Exact invalidation keeps allocator globals fixed, so the node set cannot grow.
private theorem invalidate_return {F : Type} (s : PanSemStateFiniteExact 64 F)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (post : PanSemStateFiniteExact 64 F)
    (v : ValueHOL 64) (hp : leafTagged s)
    (hq : NodeFnExit ["nd"] (fun _ _ => True) (callEntryStateHOLFinite s callee)
      (some (.returned v)) post)
    (he : post = { clearCache (callEntryStateHOLFinite s callee)
      (locN (callEntryStateHOLFinite s callee) "nd") with
      locals := post.locals, clock := post.clock })
    (hparam : callee.lookup (ofString "nd") = s.locals.lookup (ofString "node")) :
    leafTagged { post with locals := s.locals } := by
  let entry := callEntryStateHOLFinite s callee
  have hn : locN entry "nd" = locN s "node" := by
    simp only [entry, locN, callEntryStateHOLFinite, hparam]
  obtain ⟨ha, hh, hs, hq⟩ := hq (Or.inl ⟨v, rfl⟩)
  obtain ⟨har, hle, Nd, hheap, hkind, hkey⟩ := hp.1
  obtain ⟨Nd', hheap', hsub, hk, hnew, _⟩ :=
    hq Nd hheap (fun n hm => by
      have h : n = "nd" := by simpa using hm
      subst n
      rw [hn]
      exact Or.inr hkind.1) trivial
  have hg : post.globals = s.globals := by rw [he]; rfl
  have hsub' : ∀ n ∈ Nd', n ∈ Nd := by
    intro n hm
    rcases hnew n hm with h | h
    · exact h
    · have hb := nodeSize_pos (memW post n)
      dsimp only [Inside, nodeIvl] at h
      have hh : globN post "heap_ptr" = globN entry "heap_ptr" := by simp only [globN, hg, entry, callEntryStateHOLFinite]
      change globN entry "heap_ptr" ≤ n ∧ n + nodeSize (memW post n) ≤ globN post "heap_ptr" at h
      rw [hh] at h
      omega
  have hkey' := invalidation_key (s := entry) hheap
    (show locN entry "nd" ∈ Nd by rw [hn]; exact hkind.1) he hsub' hk
    (show KeyIn entry Nd (locN s "key" + locN s "level")
      (locN s "klen" - locN s "level") from hkey)
  refine ⟨⟨(arenaReady_with_locals post s.locals post.clock).2 ha, hle, Nd', hheap', ?_, hkey'⟩,
    hp.2⟩
  exact ⟨hsub _ hkind.1, (hk _ hkind.1).trans hkind.2⟩

private theorem leaf_invalidate (h : MptInsertCallees) :
    Hoare leafTagged (.call (some (none, none)) (ofString "node_invalidate")
      [.var .local (ofString "node")]) (fallPost leafTagged) := by
  refine fall_call none (specs_and h.nf_node_invalidate h.iz_node_invalidate)
    invalidate_entry ?_
  intro F s vs b callee ret post v hc hp ha hl hq
  exact invalidate_return s callee post v hp hq.1 (hq.2 (Or.inl ⟨v, rfl⟩))
    (invalidate_param s vs b callee ret hc ha hl)

private theorem lookup_insert_leaf : originalRuntimeCode.lookup (ofString "_insert_into_leaf") =
    some ((sourceFunctionEntry Guest.Software.guestFn__insert_into_leaf).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 273 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn__insert_into_leaf) rfl

private theorem eval_add_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (a b : String) (v : ValueHOL 64)
    (hv : evalAt s (.op .add [.var .local (ofString a), .var .local (ofString b)]) = some v) :
    ∃ x y : BitVec 64, s.locals.lookup (ofString a) = some (.val (.word x)) ∧
      s.locals.lookup (ofString b) = some (.val (.word y)) ∧ v = .val (.word (x + y)) := by
  rcases ha : s.locals.lookup (ofString a) with _ | va
  · simp [evalAt, evalHOLExact, evalListHOLExact, ha] at hv
  rcases va with ⟨⟨x⟩⟩ | fs | ⟨n, fs⟩
  · rcases hb : s.locals.lookup (ofString b) with _ | vb
    · simp [evalAt, evalHOLExact, evalListHOLExact, ha, hb] at hv
    rcases vb with ⟨⟨y⟩⟩ | gs | ⟨m, gs⟩
    · refine ⟨x, y, rfl, rfl, ?_⟩
      simpa [evalAt, evalHOLExact, evalListHOLExact, ha, hb, valueIsWord, valueWord,
        wordOpHOL, wordOp] using hv.symm
    · simp [evalAt, evalHOLExact, evalListHOLExact, ha, hb, valueIsWord] at hv
    · simp [evalAt, evalHOLExact, evalListHOLExact, ha, hb, valueIsWord] at hv
  · cases hb : s.locals.lookup (ofString b) <;>
      simp [evalAt, evalHOLExact, evalListHOLExact, ha, hb, valueIsWord] at hv
  · cases hb : s.locals.lookup (ofString b) <;>
      simp [evalAt, evalHOLExact, evalListHOLExact, ha, hb, valueIsWord] at hv

private theorem eval_sub_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (a b : String) (v : ValueHOL 64)
    (hv : evalAt s (.op .sub [.var .local (ofString a), .var .local (ofString b)]) = some v) :
    ∃ x y : BitVec 64, s.locals.lookup (ofString a) = some (.val (.word x)) ∧
      s.locals.lookup (ofString b) = some (.val (.word y)) ∧ v = .val (.word (x - y)) := by
  rcases ha : s.locals.lookup (ofString a) with _ | va
  · simp [evalAt, evalHOLExact, evalListHOLExact, ha] at hv
  rcases va with ⟨⟨x⟩⟩ | fs | ⟨n, fs⟩
  · rcases hb : s.locals.lookup (ofString b) with _ | vb
    · simp [evalAt, evalHOLExact, evalListHOLExact, ha, hb] at hv
    rcases vb with ⟨⟨y⟩⟩ | gs | ⟨m, gs⟩
    · refine ⟨x, y, rfl, rfl, ?_⟩
      simpa [evalAt, evalHOLExact, evalListHOLExact, ha, hb, valueIsWord, valueWord,
        wordOpHOL, wordOp] using hv.symm
    · simp [evalAt, evalHOLExact, evalListHOLExact, ha, hb, valueIsWord] at hv
    · simp [evalAt, evalHOLExact, evalListHOLExact, ha, hb, valueIsWord] at hv
  · cases hb : s.locals.lookup (ofString b) <;>
      simp [evalAt, evalHOLExact, evalListHOLExact, ha, hb, valueIsWord] at hv
  · cases hb : s.locals.lookup (ofString b) <;>
      simp [evalAt, evalHOLExact, evalListHOLExact, ha, hb, valueIsWord] at hv

private def insertArgs : List (ExpHOL 64) :=
  [.var .local (ofString "node"),
   .op .add [.var .local (ofString "key"), .var .local (ofString "level")],
   .op .sub [.var .local (ofString "klen"), .var .local (ofString "level")],
   .var .local (ofString "vptr"), .var .local (ofString "vlen")]

-- Successful argument evaluation handles missing/nonword locals. A nonempty key
-- supplies the address bound needed to turn machine addition into natural addition.
private theorem insert_entry : CallEntryOn leafTagged
    (NodeArgs ["node"] (fun s Nd => NodeKind s Nd "node" 1 ∧
      KeyIn s Nd (locN s "rk") (locN s "rl")))
    (ofString "_insert_into_leaf") insertArgs := by
  classical
  intro F s vs b callee ret hc hp ha hl
  have hm := callee_map s _ _ _ _ vs b callee ret (by rw [hc]; exact lookup_insert_leaf) hl
  change callee.lookup = List.foldl
    (fun (m : MlS → Option (ValueHOL 64)) (e : MlS × ValueHOL 64) =>
      fun n => if n = e.1 then some e.2 else m n)
    (fun _ => none) ([ofString "node", ofString "rk", ofString "rl", ofString "vptr", ofString "vlen"].zip vs) at hm
  rw [evalListHOLFinite_eq_toExact] at ha
  change evalListHOLExact s.toExact insertArgs = some vs at ha
  unfold insertArgs at ha
  rcases hn : evalAt s (.var .local (ofString "node")) with _ | vn
  · simp [evalListHOLExact, hn] at ha
  rcases hk : evalAt s (.op .add [.var .local (ofString "key"), .var .local (ofString "level")]) with _ | vk
  · simp [evalListHOLExact, hn, hk] at ha
  rcases hr : evalAt s (.op .sub [.var .local (ofString "klen"), .var .local (ofString "level")]) with _ | vr
  · simp [evalListHOLExact, hn, hk, hr] at ha
  rcases hv : evalAt s (.var .local (ofString "vptr")) with _ | vv
  · simp [evalListHOLExact, hn, hk, hr, hv] at ha
  rcases hw : evalAt s (.var .local (ofString "vlen")) with _ | vw
  · simp [evalListHOLExact, hn, hk, hr, hv, hw] at ha
  simp only [evalListHOLExact, hn, hk, hr, hv, hw, Option.some.injEq] at ha
  subst vs
  obtain ⟨key, level, hkey, hlevel, rfl⟩ := eval_add_locals s "key" "level" vk hk
  obtain ⟨klen, level', hklen, hlevel', rfl⟩ := eval_sub_locals s "klen" "level" vr hr
  have he : level' = level := by rw [hlevel] at hlevel'; cases hlevel'; rfl
  subst level'
  have hnode : locN (callEntryStateHOLFinite s callee) "node" = locN s "node" := by
    change s.locals.lookup (ofString "node") = some vn at hn
    have hcnode : callee.lookup (ofString "node") = some vn := by simp [hm, ofString]
    simp only [locN, callEntryStateHOLFinite, hcnode]
    simp only [hn]
  have hrk : locN (callEntryStateHOLFinite s callee) "rk" = (key + level).toNat := by
    simp [locN, callEntryStateHOLFinite, hm, ofString]
  have hrl : locN (callEntryStateHOLFinite s callee) "rl" = (klen - level).toNat := by
    simp [locN, callEntryStateHOLFinite, hm, ofString]
  obtain ⟨har, hle, Nd, hh, hkind, hki⟩ := hp.1
  have hln : locN s "level" = level.toNat := by simp [locN, hlevel]
  have hkn : locN s "key" = key.toNat := by simp [locN, hkey]
  have hkln : locN s "klen" = klen.toNat := by simp [locN, hklen]
  have hsub : (klen - level).toNat = locN s "klen" - locN s "level" := by
    rw [hkln, hln]
    exact BitVec.toNat_sub_of_le (by simpa only [BitVec.le_def, hkln, hln] using hle)
  refine ⟨(arenaReady_with_locals s callee (s.clock - 1)).2 har, Nd, hh, ?_, ?_, ?_⟩
  · intro n hn
    have hn' : n = "node" := by simpa using hn
    subst n
    rw [hnode]
    exact Or.inr hkind.1
  · change locN _ "node" ∈ Nd ∧ memW s (locN _ "node") = 1
    rw [hnode]
    exact hkind
  · rw [hrk, hrl, hsub]
    rcases hki with hz | ⟨hnib, ha, hi, hd⟩
    · exact Or.inl hz
    have hfit : locN s "key" + locN s "level" < 2^64 := by
      have hh : heapLimit < 2^64 := by decide
      obtain ⟨_, _⟩ := hi
      omega
    have heq : (key + level).toNat = locN s "key" + locN s "level" := by
      rw [BitVec.toNat_add, ← hkn, ← hln, Nat.mod_eq_of_lt hfit]
    rw [heq]
    exact Or.inr ⟨hnib, ha, hi, hd⟩

private theorem leaf_insert (h : MptInsertCallees) :
    Hoare leafTagged (.call (some (some (.local, ofString "r"), none))
      (ofString "_insert_into_leaf") insertArgs) (fallPost leafDone) := by
  refine fall_call (some (ofString "r")) h.nf__insert_into_leaf insert_entry ?_
  intro F s vs b callee ret post v hc hp ha hl hq
  have har := (hq (Or.inl ⟨v, rfl⟩)).1
  refine ⟨(arenaReady_with_locals post _ post.clock).2 har, ?_⟩
  change locN (setVarHOLFinite (ofString "r") v s) "go" = 0
  rw [locN_setVar_ne s "go" (ofString "r") v (by decide)]
  exact hp.2.1

private theorem cond_eq_true {F : Type} {s : PanSemStateFiniteExact 64 F} {n : String}
    {k : BitVec 64} (h : CondTrue (.cmp .equal (.var .local (ofString n)) (.const k)) s) :
    locN s n = k.toNat := by
  obtain ⟨w, hw, hn⟩ := h
  obtain ⟨a, b, ha, hb, rfl⟩ := cond_local s _ n _ w hw
  cases evalAt_const s k _ hb
  rw [← ha]
  have he : a = k := by
    simpa [Flapjack.Compiler.Encoders.Asm.wordCmpHOL] using hn
  rw [he]

private theorem cond_eq_false {F : Type} {s : PanSemStateFiniteExact 64 F} {n : String}
    {k : BitVec 64} (h : CondFalse (.cmp .equal (.var .local (ofString n)) (.const k)) s) :
    locN s n ≠ k.toNat := by
  obtain ⟨a, b, ha, hb, hz⟩ := cond_local s _ n _ 0 h
  cases evalAt_const s k _ hb
  rw [← ha]
  intro he
  have he' : a = k := BitVec.eq_of_toNat_eq he
  subst a
  simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hz

private theorem eval_load_node {F : Type} (s : PanSemStateFiniteExact 64 F)
    (v : ValueHOL 64)
    (h : evalAt s (.load .one (.op .add [.var .local (ofString "node"), .const 0])) = some v) :
    ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat = memW s (locN s "node") := by
  rcases hn : s.locals.lookup (ofString "node") with _ | vn
  · simp [evalAt, evalHOLExact, evalListHOLExact, hn] at h
  rcases vn with ⟨⟨n⟩⟩ | fs | ⟨nm, fs⟩
  · simp [evalAt, evalHOLExact, evalListHOLExact, hn, valueIsWord, valueWord,
      wordOpHOL, wordOp, memLoadHOLExact] at h
    cases hm : s.memory n with
    | word w =>
      exact ⟨w, by rw [← h.2, hm], by simp [memW, locN, hn, hm]⟩
  · simp [evalAt, evalHOLExact, evalListHOLExact, hn, valueIsWord] at h
  · simp [evalAt, evalHOLExact, evalListHOLExact, hn, valueIsWord] at h

private def iteYes : ProgHOL 64 → ProgHOL 64
  | .ite _ y _ => y
  | _ => .skip
private def iteNo : ProgHOL 64 → ProgHOL 64
  | .ite _ _ n => n
  | _ => .skip
private def leafInner := mptDecBody (mptDecBody (mptDecBody (mptDecBody mptInsertBody)))
private def leafChoice := mptLeft (mptRight leafInner)
private def leafNull := iteYes leafChoice
private def leafTail := mptRight (mptRight leafInner)
private def leafNonNull := mptDecBody (iteNo leafChoice)
private def leafOther := iteNo (mptRight (mptRight leafNonNull))

-- Reconstruct the canonical AST without assuming any other kind shard.
private theorem leaf_body_shape : mptInsertBody =
    .dec (ofString "r") .one (.const 0)
    (.dec (ofString "next_node") .one (.const 0)
    (.dec (ofString "next_slot") .one (.const 0)
    (.dec (ofString "next_level") .one (.const 0)
      (.seq (.assign .local (ofString "go") (.const 0))
      (.seq (.ite (.cmp .equal (.var .local (ofString "node")) (.const 0)) leafNull
        (.dec (ofString "k") .one
          (.load .one (.op .add [.var .local (ofString "node"), .const 0]))
          (.seq (.ite (.cmp .equal (.var .local (ofString "k")) (.const 0))
            (.call (some (none, none)) (ofString "mpt_fail") [.const 2]) .skip)
          (.seq (.call (some (none, none)) (ofString "node_invalidate") [.var .local (ofString "node")])
          (.ite (.cmp .equal (.var .local (ofString "k")) (.const 1))
            (.call (some (some (.local, ofString "r"), none)) (ofString "_insert_into_leaf") insertArgs)
            leafOther))))) leafTail))))) := rfl

private theorem tail_done : Hoare leafDone leafTail (fallPost leafDone) := by
  change Hoare leafDone
    (.seq (.ite (.cmp .equal (.var .local (ofString "slot")) (.const 0))
      (.assign .local (ofString "result") (.var .local (ofString "r")))
      (.store (.var .local (ofString "slot")) (.var .local (ofString "r"))))
    (.seq (.assign .local (ofString "node") (.var .local (ofString "next_node")))
    (.seq (.assign .local (ofString "slot") (.var .local (ofString "next_slot")))
      (.assign .local (ofString "level") (.var .local (ofString "next_level")))))) (fallPost leafDone)
  refine fall_seq (fall_ite ?_ ?_) (fall_seq (done_assign "node" _ (by decide))
    (fall_seq (done_assign "slot" _ (by decide)) (done_assign "level" _ (by decide))))
  · exact Hoare.mono (done_assign "result" _ (by decide)) (fun _ h => h.1)
  · exact Hoare.mono (done_store _ _) (fun _ h => h.1)

private theorem ready_set {F : Type} (s : PanSemStateFiniteExact 64 F)
    (n : MlS) (v : ValueHOL 64)
    (hn : ∀ m ∈ ["node", "key", "klen", "level"], ofString m ≠ n)
    (hp : leafReady s) : leafReady (setVarHOLFinite n v s) :=
  ready_locals s _ s.clock (fun m hm => by
    simp [HolFiniteMapExact.update, FUPDATE, Ne.symm (hn m hm)]) hp

private theorem ready_dec {p : ProgHOL 64} (n : MlS)
    (hn : ∀ m ∈ ["node", "key", "klen", "level"], ofString m ≠ n)
    (hg : ofString "go" ≠ n)
    (hp : Hoare leafReady p (fallPost leafDone)) :
    Hoare leafReady (.dec n .one (.const 0) p) (fallPost leafDone) :=
  fall_dec (fun m hm => by
    have he : m = "go" := by simpa using hm
    subst m
    exact hg)
    done_locals (fun s v hs _ => ready_set s n v hn hs) hp

private def leafRunning : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => leafReady s ∧ locN s "go" = 0

private theorem leaf_iteration (h : MptInsertCallees) :
    Hoare leafReady mptInsertBody (fallPost leafDone) := by
  rw [leaf_body_shape]
  refine ready_dec (ofString "r") (by decide) (by decide)
    (ready_dec (ofString "next_node") (by decide) (by decide)
    (ready_dec (ofString "next_slot") (by decide) (by decide)
    (ready_dec (ofString "next_level") (by decide) (by decide) ?_)))
  refine fall_seq (R := leafRunning) (fall_assign ?_) (fall_seq ?_ tail_done)
  · intro F s v hp hv
    cases evalAt_const s 0 v hv
    exact ⟨ready_set s _ _ (by decide) hp, locN_setVar_same s "go" 0⟩
  refine fall_ite (Hoare.of_false ?_) ?_
  · intro F s hp
    obtain ⟨har, hle, Nd, hh, hk, hkey⟩ := hp.1.1
    have hz := cond_eq_true hp.2
    have hi := (hh.1 _ hk.1).2.2.1.1
    change sourceBase ≤ locN s "node" at hi
    have hb : 0 < sourceBase := by decide
    change locN s "node" = 0 at hz
    omega
  refine fall_dec (names := ["go"]) (R := leafTagged) (by decide) done_locals ?_ ?_
  · intro F s v hp hv
    obtain ⟨w, rfl, hw⟩ := eval_load_node s v hv
    obtain ⟨har, hle, Nd, hh, hk, hkey⟩ := hp.1.1
    have hw1 : w = 1 := BitVec.eq_of_toNat_eq (by simpa [hk.2] using hw)
    subst w
    exact ⟨ready_set s _ _ (by decide) hp.1.1,
      (locN_setVar_ne s "go" (ofString "k") _ (by decide)).trans hp.1.2,
      locN_setVar_same s "k" 1⟩
  refine fall_seq (R := leafTagged) (fall_ite (Hoare.of_false ?_) ?_)
    (fall_seq (leaf_invalidate h) (fall_ite ?_ (Hoare.of_false ?_)))
  · intro F s hp
    have he := cond_eq_true hp.2
    have hk := hp.1.2.2
    change locN s "k" = 0 at he
    omega
  · exact Hoare.mono fall_skip (fun _ hp => hp.1)
  · exact Hoare.mono (leaf_insert h) (fun _ hp => hp.1)
  · intro F s hp
    have he := cond_eq_false hp.2
    exact he hp.1.2.2

/-- One iteration with node tag 1; shard 0 includes the null-root case.
Prove the bound and the continuing-state effect. No other kind shard is imported. -/
theorem mptInsert_kind1 (h : MptInsertCallees) :
    MptStepAt MptInsertActive MptInsertHead MptInsertEffect mptInsertBody mptInsertCost 1 := by
  intro F s hc hp hk
  obtain ⟨hle, Nd, hh, hr, hkey, hslot⟩ := hp.1.2 hp.2
  have hn : locN s "node" ≠ 0 := by
    intro hz
    simp [mptKind, hz] at hk
  have hm : locN s "node" ∈ Nd := hr.resolve_left hn
  have hkind : memW s (locN s "node") = 1 := by simpa only [mptKind, if_neg hn] using hk
  have hready : leafReady s := ⟨hp.1.1, hle, Nd, hh, ⟨hm, hkind⟩, hkey⟩
  have hb := insert_bounded h
  unfold TerminatingProgBoundedOn at hb
  refine ⟨hb s hc hp.1.1.1, ?_⟩
  intro hf
  have hnt : (evaluateHOLFiniteState s mptInsertBody).1 ≠ some .timeOut := by
    rcases hf with hf | hf <;> rw [hf] <;> simp
  have hfacts := (leaf_iteration h).run s hc hready hnt
  have hnone : (evaluateHOLFiniteState s mptInsertBody).1 = none := hf.resolve_right hfacts.2
  obtain ⟨ha, hg⟩ := hfacts.1 hnone
  exact ⟨⟨ha, fun h => (h hg).elim⟩, Or.inl hg⟩


end InitECandidate.Solver.Wave8GuestInv.GuardedBody
