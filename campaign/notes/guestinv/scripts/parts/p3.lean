/-! ## 4. Bridge: covered entry ⊨ `GuestInv`, and guarded `main` ⇒ covered clock bound -/

/-- A declaration is either not a global, or a global initialised to the constant `0`. -/
def zeroGlobalDecl : DeclHOL 64 → Bool
  | .decl _ _ (.const c) => c == 0
  | .decl _ _ _ => false
  | _ => true

def declGlobalNames : List (DeclHOL 64) → List MlS
  | [] => []
  | .decl _ n _ :: ds => n :: declGlobalNames ds
  | _ :: ds => declGlobalNames ds

theorem evaluateDecls_zero_globals {σ : Type} :
    ∀ (decls : List (DeclHOL 64)) (s s' : PanSemStateFiniteExact 64 σ)
      (h : DecidablePred s.memaddrs),
      @evaluateDeclsHOLFinite 64 σ _ s h decls = some s' →
      decls.all zeroGlobalDecl = true →
      ∀ name : MlS, (s.globals.lookup name = some (.val (.word 0)) ∨ name ∈ declGlobalNames decls) →
        s'.globals.lookup name = some (.val (.word 0)) := by
  intro decls
  induction decls with
  | nil =>
    intro s s' h run _ name hn
    simp only [evaluateDeclsHOLFinite, Option.some.injEq] at run
    subst run
    simpa [declGlobalNames] using hn
  | cons d rest ih =>
    intro s s' h run hall name hn
    simp only [List.all_cons, Bool.and_eq_true] at hall
    obtain ⟨hd, hrest⟩ := hall
    cases d with
    | name _ _ =>
      simp only [evaluateDeclsHOLFinite] at run
      exact ih s s' h run hrest name (by simpa [declGlobalNames] using hn)
    | decl shape n e =>
      cases e with
      | const c =>
        simp only [zeroGlobalDecl, beq_iff_eq] at hd
        subst hd
        simp only [evaluateDeclsHOLFinite] at run
        split at run
        · rename_i v hv
          have hv' : some (ValueHOL.val (HolWordLab.word (0 : BitVec 64))) = some v := hv
          cases hv'
          split at run
          · refine ih _ s' _ run hrest name ?_
            by_cases hname : name = n
            · subst hname
              left
              simp [setGlobalHOLFinite, FUPDATE]
            · simp only [declGlobalNames, List.mem_cons, hname, false_or] at hn
              rcases hn with hn | hn
              · left
                simp [setGlobalHOLFinite, FUPDATE, Ne.symm hname, hn]
              · right; exact hn
          · cases run
        · cases run
      | _ => simp [zeroGlobalDecl] at hd
    | function fi =>
      simp only [evaluateDeclsHOLFinite] at run
      split at run
      · exact ih _ s' _ run hrest name (by simpa [declGlobalNames] using hn)
      · cases run
    | exnDecl en sh =>
      simp only [evaluateDeclsHOLFinite] at run
      split at run
      · exact ih _ s' _ run hrest name (by simpa [declGlobalNames] using hn)
      · cases run

/-- Decl-level counterpart of `zeroGlobalDecl` (cheap to `decide` on the literal AST). -/
def zeroDeclAst : Decl (BitVec 64) → Bool
  | .decl _ _ (.const c) => c == 0
  | .decl _ _ _ => false
  | _ => true

theorem zeroGlobalDecl_declToHOL (d : Decl (BitVec 64)) :
    zeroGlobalDecl (declToHOL d) = zeroDeclAst d := by
  cases d with
  | decl shape name e => cases e <;> simp [declToHOL, expToHOL, zeroGlobalDecl, zeroDeclAst]
  | _ => rfl

theorem guestAst_zero : Guest.Software.guestAst.all zeroDeclAst = true := by decide

theorem mem_guestAst_of_mem_sourceDeclarations {d : DeclHOL 64} (h : d ∈ sourceDeclarations) :
    d ∈ Guest.Software.guestAst.map declToHOL := by
  unfold sourceDeclarations at h
  obtain ⟨before, fi, rest, hsplit, _, hmoved⟩ :=
    Flapjack.Pancake.PanToTarget.mainFirstHOL_of_main
      (Guest.Software.guestAst.map declToHOL) sourceHasMain
  rw [hmoved] at h
  rw [hsplit]
  rcases List.mem_cons.mp h with rfl | h
  · exact List.mem_append_right _ List.mem_cons_self
  · rcases List.mem_append.mp h with hb | hr
    · exact List.mem_append_left _ hb
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr)

theorem sourceDeclarations_zero : sourceDeclarations.all zeroGlobalDecl = true := by
  rw [List.all_eq_true]
  intro d hd
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (mem_guestAst_of_mem_sourceDeclarations hd)
  rw [zeroGlobalDecl_declToHOL]
  exact List.all_eq_true.mp guestAst_zero a ha

theorem mem_declGlobalNames {shape : ShapeHOL} {n : MlS} {e : ExpHOL 64} :
    ∀ {l : List (DeclHOL 64)}, DeclHOL.decl shape n e ∈ l → n ∈ declGlobalNames l
  | [], h => by cases h
  | d :: ds, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact List.mem_cons_self
    · have ih := mem_declGlobalNames h
      cases d <;> simp only [declGlobalNames] <;> first | exact ih | exact List.mem_cons_of_mem _ ih

theorem guestGlobalNames_declared :
    ∀ n ∈ guestGlobalNames, ofString n ∈ declGlobalNames sourceDeclarations := by
  intro n hn
  rw [← astGlobalNames_eq] at hn
  obtain ⟨d, hd, hdn⟩ := List.mem_filterMap.mp hn
  cases d with
  | decl shape name e =>
    simp only [Option.some.injEq] at hdn
    subst hdn
    exact mem_declGlobalNames
      (GuestCodeLookup.mem_sourceDeclarations_of_mem (List.mem_map.mpr ⟨_, hd, rfl⟩))
  | _ => simp at hdn

/-- The 67 global declarations evaluate to the word `0` (each is `Decl.decl Shape.one n (const 0)`). -/
theorem postDecls_globals (input : Guest.InputBlob) (stCtxt : StructContextExact)
    (s_decls : PanSemStateFiniteExact 64 Guest.HostMemory)
    (hdecls : @evaluateDeclsHOLFinite 64 Guest.HostMemory _
      { sourceInitialState input with structs := stCtxt }
      (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a))
      sourceDeclarations = some s_decls) :
    ∀ name ∈ guestGlobalNames, GlobalWord s_decls name 0 := fun name hn =>
  evaluateDecls_zero_globals sourceDeclarations _ s_decls _ hdecls sourceDeclarations_zero
    (ofString name) (Or.inr (guestGlobalNames_declared name hn))

/-- The covered post-declarations state satisfies `GuestInv` (four metadata fields). -/
theorem guestInv_postDecls (input : Guest.InputBlob) (stCtxt : StructContextExact)
    (s_decls : PanSemStateFiniteExact 64 Guest.HostMemory)
    (hdecls : @evaluateDeclsHOLFinite 64 Guest.HostMemory _
      { sourceInitialState input with structs := stCtxt }
      (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a))
      sourceDeclarations = some s_decls) :
    GuestInv s_decls := by
  have hmeta := B2PostDecls.evaluateDecls_meta sourceDeclarations
    { sourceInitialState input with structs := stCtxt } s_decls
    (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a)) hdecls
  refine ⟨?_, hmeta.memaddrs, hmeta.shMemaddrs, hmeta.baseAddr⟩
  rw [hmeta.code]
  exact B2PostDecls.map_ext rfl

theorem coveredFfi_postDecls (input : Guest.InputBlob) (stCtxt : StructContextExact)
    (s_decls : PanSemStateFiniteExact 64 Guest.HostMemory)
    (hgas : Guest.GasLimit.declaredGasLimit input ≤ maxCoveredGas)
    (hdecls : @evaluateDeclsHOLFinite 64 Guest.HostMemory _
      { sourceInitialState input with structs := stCtxt }
      (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a))
      sourceDeclarations = some s_decls) :
    CoveredFfi s_decls := by
  have hmeta := B2PostDecls.evaluateDecls_meta sourceDeclarations
    { sourceInitialState input with structs := stCtxt } s_decls
    (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a)) hdecls
  refine ⟨rfl, input, hgas, ?_⟩
  change OracleConsistent sourceOracle (Guest.guestHostMemory input) s_decls.ffi
  rw [hmeta.ffi]
  exact initial_oracle_consistent sourceOracle (Guest.guestHostMemory input)

/-- Generic bridge: any guard `P` that holds at every covered `main` entry state.
Proof adapted from the repaired `coveredSourceTicksConsumedBounded_of_terminatingMain`. -/
theorem coveredSourceTicksConsumedBounded_of_terminatingMainOnP
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {K : Nat}
    (hmain : TerminatingFunBoundedOn P (ofString "main") K)
    (hentry : ∀ (input : Guest.InputBlob) (stCtxt : StructContextExact)
      (s_decls : PanSemStateFiniteExact 64 Guest.HostMemory) (k : Nat)
      (callee : HolFiniteMapExact MlS (ValueHOL 64)),
      Guest.GasLimit.declaredGasLimit input ≤ maxCoveredGas →
      @evaluateDeclsHOLFinite 64 Guest.HostMemory _
        { sourceInitialState input with structs := stCtxt }
        (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a))
        sourceDeclarations = some s_decls →
      P (callEntryStateHOLFinite { s_decls with clock := k } callee)) :
    CoveredSourceTicksConsumedBounded (K + 1) := by
  obtain ⟨params, body, retShape, hlook, hbody⟩ := hmain
  have hparams : params = [] := by
    rw [lookup_main] at hlook
    have h1 := congrArg Prod.fst (Option.some.inj hlook)
    exact h1.symm.trans rfl
  subst hparams
  intro input outcome events hgas _hsource _hcov stCtxt s_decls _hst hdecls k res s_post hrun hnt
  have hmeta := B2PostDecls.evaluateDecls_meta sourceDeclarations
    { sourceInitialState input with structs := stCtxt } s_decls
    (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a)) hdecls
  have hcode : s_decls.code = originalRuntimeCode := by
    rw [hmeta.code]
    exact B2PostDecls.map_ext rfl
  rw [evaluateHOLFiniteState_call] at hrun
  have hargs : evalListHOLFinite { s_decls with clock := k }
      (h := fun a => Classical.propDecidable (({ s_decls with clock := k } :
        PanSemStateFiniteExact 64 Guest.HostMemory).memaddrs a)) [] = some [] := rfl
  rw [hargs] at hrun
  dsimp only at hrun
  obtain ⟨callee, hlookup_call⟩ : ∃ callee,
      PanSemStateFiniteExact.lookupCodeHOLFinite s_decls.code.lookup (ofString "main") [] =
        some (body, callee, retShape) := by
    rw [hcode]
    rcases hx : PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup
        (ofString "main") [] with _ | ⟨b, c, r⟩
    · rw [PanSemStateFiniteExact.lookupCodeHOLFinite_eq_none_iff] at hx
      simp [lookupCodeHOLExact, hlook] at hx
    · have hx' := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some _ _ _ _ _ _ hx
      simp [lookupCodeHOLExact, hlook] at hx'
      obtain ⟨rfl, -, rfl⟩ := hx'
      exact ⟨c, rfl⟩
  rw [hlookup_call] at hrun
  dsimp only at hrun
  by_cases hk0 : k = 0
  · subst hk0
    simp at hrun
    rcases hrun with ⟨rfl, _⟩
    exact absurd rfl hnt
  · simp only [hk0, ↓reduceIte] at hrun
    let entry := callEntryStateHOLFinite { s_decls with clock := k } callee
    have hentry_code : entry.code = originalRuntimeCode := hcode
    have hentry_P : P entry := hentry input stCtxt s_decls k callee hgas hdecls
    rcases hb_run : evaluateHOLFiniteState entry body with ⟨bres, bpost⟩
    rw [hb_run] at hrun
    have hb_nt : bres ≠ some .timeOut := by
      intro hbt
      subst hbt
      simp at hrun
      rcases hrun with ⟨rfl, _⟩
      exact hnt rfl
    have hb_bound := hbody entry hentry_code hentry_P (by rw [hb_run]; exact hb_nt)
    rw [hb_run] at hb_bound
    obtain ⟨hspent, _⟩ := hb_bound
    have hentry_clk : entry.clock = k - 1 := rfl
    dsimp only at hspent
    have hpost_clk : s_post.clock = bpost.clock := by
      cases bres with
      | none => simp at hrun; obtain ⟨_, rfl⟩ := hrun; rfl
      | some r =>
        cases r <;> simp [emptyLocalsHOLFinite] at hrun
        all_goals (try split at hrun) <;> obtain ⟨_, rfl⟩ := hrun <;> rfl
    omega

/-- Main bridge (the replacement of `coveredSourceTicksConsumedBounded_of_terminatingMain`). -/
theorem coveredSourceTicksConsumedBounded_of_terminatingMainOn {K : Nat}
    (hmain : TerminatingFunBoundedOn GuestInv (ofString "main") K) :
    CoveredSourceTicksConsumedBounded (K + 1) :=
  coveredSourceTicksConsumedBounded_of_terminatingMainOnP hmain
    fun input stCtxt s_decls k callee _ hdecls =>
      guestInv_callEntry _ callee
        (guestInv_with_locals_clock s_decls s_decls.locals k
          (guestInv_postDecls input stCtxt s_decls hdecls))

/-- Covered variant: the guarded main bound may also use the covered input (gas ≤ 2·10^8). -/
theorem coveredSourceTicksConsumedBounded_of_terminatingMainOnCovered {K : Nat}
    (hmain : TerminatingFunBoundedOn GuestInvCovered (ofString "main") K) :
    CoveredSourceTicksConsumedBounded (K + 1) :=
  coveredSourceTicksConsumedBounded_of_terminatingMainOnP hmain
    fun input stCtxt s_decls k callee hgas hdecls =>
      ⟨guestInv_callEntry _ callee
        (guestInv_with_locals_clock s_decls s_decls.locals k
          (guestInv_postDecls input stCtxt s_decls hdecls)),
       coveredFfi_postDecls input stCtxt s_decls hgas hdecls⟩

/-- `main`-only entry guard: the covered entry also fixes memory to the bootstrap image
(`sourceMemory`: 40-byte startup header, zero elsewhere). `alloc` never zeroes, so `main`
may rely on fresh heap cells being `0`; no leaf below `main` gets this conjunct. -/
def InitialMemory : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => s.memory = sourceMemory

/-- All 67 globals still hold their declaration value `0`. -/
def GlobalsZero : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ∀ name ∈ guestGlobalNames, GlobalWord s name 0

/-- THE TOP OBLIGATION's guard. `main` is entered exactly once, from the covered
post-declarations state; this guard records everything that is true there: `GuestInv`, the
covered FFI (header gas ≤ 2·10^8), the bootstrap memory image and all globals = 0. It is
strictly stronger than `GuestInv`; only `main` gets it (every other leaf is guarded by
`GuestInv` or by a §7 contract). The campaign target `CoveredSourceTicksConsumedBounded K_pan`
follows from `TerminatingFunBoundedOn MainEntry "main" K.main` alone (bridge below). -/
def MainEntry : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => GuestInvCovered s ∧ InitialMemory s ∧ GlobalsZero s

theorem initialMemory_postDecls (input : Guest.InputBlob) (stCtxt : StructContextExact)
    (s_decls : PanSemStateFiniteExact 64 Guest.HostMemory) (k : Nat)
    (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (hdecls : @evaluateDeclsHOLFinite 64 Guest.HostMemory _
      { sourceInitialState input with structs := stCtxt }
      (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a))
      sourceDeclarations = some s_decls) :
    InitialMemory (callEntryStateHOLFinite { s_decls with clock := k } callee) :=
  (B2PostDecls.evaluateDecls_meta sourceDeclarations
    { sourceInitialState input with structs := stCtxt } s_decls
    (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a)) hdecls).memory

/-- Strongest bridge: guarded by the exact covered entry shape (used for `K_pan`). -/
theorem coveredSourceTicksConsumedBounded_of_terminatingMainOnEntry {K : Nat}
    (hmain : TerminatingFunBoundedOn MainEntry (ofString "main") K) :
    CoveredSourceTicksConsumedBounded (K + 1) :=
  coveredSourceTicksConsumedBounded_of_terminatingMainOnP hmain
    fun input stCtxt s_decls k callee hgas hdecls =>
      ⟨⟨guestInv_callEntry _ callee
          (guestInv_with_locals_clock s_decls s_decls.locals k
            (guestInv_postDecls input stCtxt s_decls hdecls)),
        coveredFfi_postDecls input stCtxt s_decls hgas hdecls⟩,
       initialMemory_postDecls input stCtxt s_decls k callee hdecls,
       fun name hn => postDecls_globals input stCtxt s_decls hdecls name hn⟩

/-- The adapter round 1 asked for: the campaign's target predicate, fully qualified (the name
`CoveredSourceTicksConsumedBounded` also occurs in other files). -/
theorem coveredTarget_of_terminatingMainOnEntry {K : Nat}
    (hmain : TerminatingFunBoundedOn MainEntry (ofString "main") K) :
    InitECandidate.Solver.UniformSourceClock.CoveredSourceTicksConsumedBounded (K + 1) :=
  coveredSourceTicksConsumedBounded_of_terminatingMainOnEntry hmain

