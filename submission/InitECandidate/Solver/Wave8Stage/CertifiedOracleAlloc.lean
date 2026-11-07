import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BackendDecomposition
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

/-! Fast structural & O(N log N) oracle register-allocation certification for large WordLang functions. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 256000000

namespace InitECandidate.Solver.Wave8Stage
open InitE Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.Wave8Stage.ConcreteM7313

def sptFoldiFast {α : Type} (f : Nat → α → List (Nat × α) → List (Nat × α))
    (index step : Nat) (accumulator : List (Nat × α)) : Spt α → List (Nat × α)
  | .ln => accumulator
  | .ls value => f index value accumulator
  | .bn left right =>
      sptFoldiFast f (index + step) (2 * step)
        (sptFoldiFast f (index + 2 * step) (2 * step) accumulator left) right
  | .bs left value right =>
      sptFoldiFast f (index + step) (2 * step)
        (f index value (sptFoldiFast f (index + 2 * step) (2 * step) accumulator left)) right

theorem sptFoldi_eq_fast {α : Type} (f : Nat → α → List (Nat × α) → List (Nat × α)) :
    ∀ (t : Spt α) (index : Nat) (acc : List (Nat × α)),
      sptFoldi f index acc t = sptFoldiFast f index (lrNext index) acc t
  | .ln, _, _ => rfl
  | .ls _, _, _ => rfl
  | .bn l r, idx, acc => by
    simp only [sptFoldi, sptFoldiFast]
    rw [sptFoldi_eq_fast f l (idx + 2 * lrNext idx) acc,
        lrNext_offset_two idx,
        sptFoldi_eq_fast f r (idx + lrNext idx) _,
        lrNext_offset_one idx]
  | .bs l v r, idx, acc => by
    simp only [sptFoldi, sptFoldiFast]
    rw [sptFoldi_eq_fast f l (idx + 2 * lrNext idx) acc,
        lrNext_offset_two idx,
        sptFoldi_eq_fast f r (idx + lrNext idx) _,
        lrNext_offset_one idx]

def sptToAListFast {α : Type} (tree : Spt α) : List (Nat × α) :=
  sptFoldiFast (fun key value accumulator => (key, value) :: accumulator) 0 1 [] tree

theorem sptToAList_eq_fast {α : Type} (tree : Spt α) :
    sptToAList tree = sptToAListFast tree := by
  unfold sptToAList sptToAListFast
  rw [sptFoldi_eq_fast]
  have h0 : lrNext 0 = 1 := by simp [lrNext]
  rw [h0]

def sptDifferenceS {α β : Type} : (left : Spt α) → Spt β → Spt α
  | .ln, _ => .ln
  | .ls value, right =>
      match right with
      | .ln => .ls value
      | .ls _ => .ln
      | .bn _ _ => .ls value
      | .bs _ _ _ => .ln
  | .bn first second, right =>
      match right with
      | .ln => .bn first second
      | .ls _ => .bn first second
      | .bn first' second' =>
          sptMkBN (sptDifferenceS first first') (sptDifferenceS second second')
      | .bs first' _ second' =>
          sptMkBN (sptDifferenceS first first') (sptDifferenceS second second')
  | .bs first value second, right =>
      match right with
      | .ln => .bs first value second
      | .ls _ => .bn first second
      | .bn first' second' =>
          sptMkBS (sptDifferenceS first first') value (sptDifferenceS second second')
      | .bs first' _ second' =>
          sptMkBN (sptDifferenceS first first') (sptDifferenceS second second')
termination_by structural left _ => left

theorem sptDifference_eq_S {α β : Type} :
    ∀ (l : Spt α) (r : Spt β), sptDifference l r = sptDifferenceS l r
  | .ln, _ => by simp [sptDifference, sptDifferenceS]
  | .ls _, r => by cases r <;> simp [sptDifference, sptDifferenceS]
  | .bn f s, r => by
    cases r <;> simp [sptDifference, sptDifferenceS, sptDifference_eq_S f, sptDifference_eq_S s]
  | .bs f v s, r => by
    cases r <;> simp [sptDifference, sptDifferenceS, sptDifference_eq_S f, sptDifference_eq_S s]

def sptUnionS {α : Type} : (left : Spt α) → Spt α → Spt α
  | .ln, right => right
  | .ls value, right =>
      match right with
      | .ln => .ls value
      | .ls _ => .ls value
      | .bn first second => .bs first value second
      | .bs first _ second => .bs first value second
  | .bn first second, right =>
      match right with
      | .ln => .bn first second
      | .ls value => .bs first value second
      | .bn first' second' => .bn (sptUnionS first first') (sptUnionS second second')
      | .bs first' value second' =>
          .bs (sptUnionS first first') value (sptUnionS second second')
  | .bs first value second, right =>
      match right with
      | .ln => .bs first value second
      | .ls _ => .bs first value second
      | .bn first' second' =>
          .bs (sptUnionS first first') value (sptUnionS second second')
      | .bs first' _ second' =>
          .bs (sptUnionS first first') value (sptUnionS second second')
termination_by structural left _ => left

theorem sptUnion_eq_S {α : Type} :
    ∀ (l r : Spt α), sptUnion l r = sptUnionS l r
  | .ln, _ => by simp [sptUnion, sptUnionS]
  | .ls _, r => by cases r <;> simp [sptUnion, sptUnionS]
  | .bn f s, r => by
    cases r <;> simp [sptUnion, sptUnionS, sptUnion_eq_S f, sptUnion_eq_S s]
  | .bs f v s, r => by
    cases r <;> simp [sptUnion, sptUnionS, sptUnion_eq_S f, sptUnion_eq_S s]

def checkColAux : List Nat → Option NumSet
  | [] => some .ln
  | name :: names =>
    match checkColAux names with
    | none => none
    | some colSet =>
      match sptLookup name colSet with
      | some () => none
      | none => some (sptInsert name () colSet)

def checkColFast {α : Type} (f : Nat → Nat) (tree : Spt α) : Option (Spt α × NumSet) :=
  match checkColAux ((sptToAListFast tree).map (fun entry => f entry.1)) with
  | none => none
  | some colSet => some (tree, colSet)

private theorem sptLookup_mem_fromAList_unit :
    ∀ (names : List Nat) (x : Nat),
      sptLookup x (sptFromAList (names.map (fun n => (n, ())))) = some () ↔ x ∈ names
  | [], x => by simp [sptFromAList]
  | n :: ns, x => by
    simp only [List.map_cons, sptFromAList, List.mem_cons]
    by_cases h : x = n
    · subst h
      simp [sptLookup_sptInsert_same]
    · rw [sptLookup_sptInsert_ne n x () _ h]
      simp [sptLookup_mem_fromAList_unit ns x, h]

private theorem checkColAux_spec :
    ∀ (names : List Nat),
      checkColAux names =
        if names.Pairwise (· ≠ ·) then
          some (sptFromAList (names.map (fun name => (name, ()))))
        else none
  | [] => by simp [checkColAux, sptFromAList]
  | n :: ns => by
    rw [checkColAux, checkColAux_spec ns]
    by_cases hpw : ns.Pairwise (· ≠ ·)
    · by_cases hmem : n ∈ ns
      · have hlookup : sptLookup n (sptFromAList (ns.map (fun name => (name, ())))) = some () :=
          (sptLookup_mem_fromAList_unit ns n).2 hmem
        have hnotpw : ¬ (n :: ns).Pairwise (· ≠ ·) := by
          rw [List.pairwise_cons]
          intro h; exact h.1 n hmem rfl
        simp [hpw, hlookup, hnotpw]
      · have hlookup : sptLookup n (sptFromAList (ns.map (fun name => (name, ())))) = none := by
          cases h : sptLookup n (sptFromAList (ns.map (fun name => (name, ())))) with
          | none => rfl
          | some u =>
            cases u
            exact False.elim (hmem ((sptLookup_mem_fromAList_unit ns n).1 h))
        have hcons : (n :: ns).Pairwise (· ≠ ·) :=
          List.pairwise_cons.2 ⟨fun a ha heq => hmem (heq ▸ ha), hpw⟩
        simp [hpw, hlookup, hcons, sptFromAList]
    · have hnotpw : ¬ (n :: ns).Pairwise (· ≠ ·) := by
        rw [List.pairwise_cons]; intro h; exact hpw h.2
      simp [hpw, hnotpw]

theorem checkCol_eq_fast {α : Type} (f : Nat → Nat) (tree : Spt α) :
    RegAlloc.checkCol f tree = checkColFast f tree := by
  unfold RegAlloc.checkCol checkColFast
  dsimp only []
  rw [sptToAList_eq_fast, checkColAux_spec]
  by_cases h : (List.map (fun entry => f entry.1) (sptToAListFast tree)).Pairwise (· ≠ ·) <;> simp [h]

def checkClashTreeFast (f : Nat → Nat) : RegAlloc.ClashTree → NumSet → NumSet →
    Option (NumSet × NumSet)
  | .delta writes reads, live, coloured =>
    match RegAlloc.checkPartialCol f writes live coloured with
    | none => none
    | some _ => RegAlloc.checkPartialCol f reads (RegAlloc.numsetListDelete writes live)
        (RegAlloc.numsetListDelete (writes.map f) coloured)
  | .set tree, _, _ => checkColFast f tree
  | .branch fixed left right, live, coloured =>
    match checkClashTreeFast f left live coloured with
    | none => none
    | some (leftOut, leftColoured) =>
      match checkClashTreeFast f right live coloured with
      | none => none
      | some (rightOut, _) =>
        match fixed with
        | none => RegAlloc.checkPartialCol f
            ((sptToAListFast (sptDifferenceS rightOut leftOut)).map Prod.fst)
            leftOut leftColoured
        | some tree => checkColFast f tree
  | .seq left right, live, coloured =>
    match checkClashTreeFast f right live coloured with
    | none => none
    | some (rightOut, rightColoured) => checkClashTreeFast f left rightOut rightColoured

theorem checkClashTree_eq_fast (f : Nat → Nat) :
    ∀ (t : RegAlloc.ClashTree) (live coloured : NumSet),
      RegAlloc.checkClashTree f t live coloured = checkClashTreeFast f t live coloured
  | .delta w r, live, col => rfl
  | .set tree, _, _ => checkCol_eq_fast f tree
  | .seq l r, live, col => by
    simp only [RegAlloc.checkClashTree, checkClashTreeFast, checkClashTree_eq_fast f r live col]
    cases checkClashTreeFast f r live col with
    | none => rfl
    | some p => exact checkClashTree_eq_fast f l p.1 p.2
  | .branch fixed l r, live, col => by
    simp only [RegAlloc.checkClashTree, checkClashTreeFast, checkClashTree_eq_fast f l live col]
    cases checkClashTreeFast f l live col with
    | none => rfl
    | some lp =>
      simp only [checkClashTree_eq_fast f r live col]
      cases checkClashTreeFast f r live col with
      | none => rfl
      | some rp =>
        cases fixed with
        | none => simp only [sptToAList_eq_fast, sptDifference_eq_S]
        | some tree => exact checkCol_eq_fast f tree

def applyNummapKeyFast {α : Type} (f : Nat → Nat) (names : Spt α) : Spt α :=
  sptFromAList ((sptToAListFast names).map (fun (key, value) => (f key, value)))

def applyNummapsKeyFast {α β : Type} (f : Nat → Nat) (names : Spt α × Spt β) : Spt α × Spt β :=
  (applyNummapKeyFast f names.1, applyNummapKeyFast f names.2)

def applyColourFast {width : Nat} [NeZero width] (f : Nat → Nat) :
    WordLangProgHOL (BitVec width) → WordLangProgHOL (BitVec width)
  | .skip => .skip
  | .move pri ls => .move pri (List.zip (ls.map (f ∘ Prod.fst)) (ls.map (f ∘ Prod.snd)))
  | .inst i => .inst (WordAlloc.applyColourInst f i)
  | .assign num exp => .assign (f num) (WordAlloc.applyColourExp f exp)
  | .get num store => .get (f num) store
  | .store exp num => .store (WordAlloc.applyColourExp f exp) (f num)
  | .call ret dest args h =>
      let ret' := match ret with
        | none => none
        | some (vs, cutset, retHandler, l1, l2) =>
            some (vs.map f, applyNummapsKeyFast f cutset, applyColourFast f retHandler, l1, l2)
      let args' := args.map f
      let h' := match h with
        | none => none
        | some (v, prog, l1, l2) => some (f v, applyColourFast f prog, l1, l2)
      .call ret' dest args' h'
  | .seq s1 s2 => .seq (applyColourFast f s1) (applyColourFast f s2)
  | .mustTerminate s1 => .mustTerminate (applyColourFast f s1)
  | .ite cmp r1 ri e2 e3 =>
      .ite cmp (f r1) (WordAlloc.applyColourImm f ri) (applyColourFast f e2) (applyColourFast f e3)
  | .install r1 r2 r3 r4 numset =>
      .install (f r1) (f r2) (f r3) (f r4) (applyNummapsKeyFast f numset)
  | .codeBufferWrite r1 r2 => .codeBufferWrite (f r1) (f r2)
  | .dataBufferWrite r1 r2 => .dataBufferWrite (f r1) (f r2)
  | .ffi ffiIndex ptr1 len1 ptr2 len2 numset =>
      .ffi ffiIndex (f ptr1) (f len1) (f ptr2) (f len2) (applyNummapsKeyFast f numset)
  | .locValue r l1 => .locValue (f r) l1
  | .alloc num numset => .alloc (f num) (applyNummapsKeyFast f numset)
  | .storeConsts a b c d ws => .storeConsts (f a) (f b) (f c) (f d) ws
  | .raise num => .raise (f num)
  | .return num1 nums => .return (f num1) (nums.map f)
  | .tick => .tick
  | .set n exp => .set n (WordAlloc.applyColourExp f exp)
  | .opCurrHeap b n1 n2 => .opCurrHeap b (f n1) (f n2)
  | .shareInst op v exp => .shareInst op (f v) (WordAlloc.applyColourExp f exp)
  | .loop names body exitNames =>
      .loop (applyNummapKeyFast f names) (applyColourFast f body) (applyNummapKeyFast f exitNames)
  | p@(.break _) => p
  | p@(.continue _) => p

theorem applyNummapKey_eq_fast {α : Type} (f : Nat → Nat) (names : Spt α) :
    WordAlloc.applyNummapKey f names = applyNummapKeyFast f names := by
  unfold WordAlloc.applyNummapKey applyNummapKeyFast
  rw [sptToAList_eq_fast]

theorem applyNummapsKey_eq_fast {α β : Type} (f : Nat → Nat) (names : Spt α × Spt β) :
    WordAlloc.applyNummapsKey f names = applyNummapsKeyFast f names := by
  unfold WordAlloc.applyNummapsKey applyNummapsKeyFast
  rw [applyNummapKey_eq_fast, applyNummapKey_eq_fast]

theorem applyColour_eq_fast {width : Nat} [NeZero width] (f : Nat → Nat) :
    ∀ (p : WordLangProgHOL (BitVec width)), WordAlloc.applyColour f p = applyColourFast f p
  | .call ret dest args h => by
    cases ret <;> cases h
    · rfl
    · rename_i hv; rcases hv with ⟨v, prog, l1, l2⟩
      simp only [WordAlloc.applyColour, applyColourFast, applyColour_eq_fast f prog]
    · rename_i r; rcases r with ⟨vs, cutset, retH, l1, l2⟩
      simp only [WordAlloc.applyColour, applyColourFast, applyNummapsKey_eq_fast, applyColour_eq_fast f retH]
    · rename_i r hv; rcases r with ⟨vs, cutset, retH, l1, l2⟩; rcases hv with ⟨v, prog, hl1, hl2⟩
      simp only [WordAlloc.applyColour, applyColourFast, applyNummapsKey_eq_fast,
        applyColour_eq_fast f retH, applyColour_eq_fast f prog]
  | .seq s1 s2 => by simp only [WordAlloc.applyColour, applyColourFast, applyColour_eq_fast f s1, applyColour_eq_fast f s2]
  | .mustTerminate s1 => by simp only [WordAlloc.applyColour, applyColourFast, applyColour_eq_fast f s1]
  | .ite cmp r1 ri e2 e3 => by simp only [WordAlloc.applyColour, applyColourFast, applyColour_eq_fast f e2, applyColour_eq_fast f e3]
  | .install r1 r2 r3 r4 numset => by simp only [WordAlloc.applyColour, applyColourFast, applyNummapsKey_eq_fast]
  | .ffi idx p1 l1 p2 l2 numset => by simp only [WordAlloc.applyColour, applyColourFast, applyNummapsKey_eq_fast]
  | .alloc num numset => by simp only [WordAlloc.applyColour, applyColourFast, applyNummapsKey_eq_fast]
  | .loop names body exitNames => by simp only [WordAlloc.applyColour, applyColourFast, applyNummapKey_eq_fast, applyColour_eq_fast f body]
  | .skip | .move _ _ | .inst _ | .assign _ _ | .get _ _ | .store _ _
  | .codeBufferWrite _ _ | .dataBufferWrite _ _ | .locValue _ _ | .storeConsts _ _ _ _ _
  | .raise _ | .return _ _ | .tick | .set _ _ | .opCurrHeap _ _ _ | .shareInst _ _ _
  | .break _ | .continue _ => rfl

def everyNameFast (predicate : Nat → Bool) (cutsets : WordLangCutsetsHOL) : Bool :=
  ((sptToAListFast cutsets.1).map Prod.fst).all predicate &&
    ((sptToAListFast cutsets.2).map Prod.fst).all predicate

def everyStackVarFast {width : Nat} [NeZero width] (predicate : Nat → Bool) :
    WordLangProgHOL (BitVec width) → Bool
  | .ffi _ _ _ _ _ names => everyNameFast predicate names
  | .install _ _ _ _ names => everyNameFast predicate names
  | .call returns _ _ handler =>
      match returns with
      | none => true
      | some (_, names, body, _, _) =>
          everyNameFast predicate names && everyStackVarFast predicate body &&
            match handler with
            | none => true
            | some (_, body, _, _) => everyStackVarFast predicate body
  | .alloc _ names => everyNameFast predicate names
  | .mustTerminate body => everyStackVarFast predicate body
  | .seq first second => everyStackVarFast predicate first && everyStackVarFast predicate second
  | .ite _ _ _ first second => everyStackVarFast predicate first && everyStackVarFast predicate second
  | .loop _ body _ => everyStackVarFast predicate body
  | _ => true

theorem everyName_eq_fast (p : Nat → Bool) (c : WordLangCutsetsHOL) :
    everyNameHOL p c = everyNameFast p c := by
  unfold everyNameHOL everyNameFast
  rw [sptToAList_eq_fast, sptToAList_eq_fast]

theorem everyStackVar_eq_fast {width : Nat} [NeZero width] (pred : Nat → Bool) :
    ∀ (p : WordLangProgHOL (BitVec width)), everyStackVarHOL pred p = everyStackVarFast pred p
  | .ffi _ _ _ _ _ names => everyName_eq_fast pred names
  | .install _ _ _ _ names => everyName_eq_fast pred names
  | .alloc _ names => everyName_eq_fast pred names
  | .mustTerminate b => everyStackVar_eq_fast pred b
  | .seq s1 s2 => by simp only [everyStackVarHOL, everyStackVarFast, everyStackVar_eq_fast pred s1, everyStackVar_eq_fast pred s2]
  | .ite _ _ _ s1 s2 => by simp only [everyStackVarHOL, everyStackVarFast, everyStackVar_eq_fast pred s1, everyStackVar_eq_fast pred s2]
  | .loop _ b _ => everyStackVar_eq_fast pred b
  | .call ret _ _ h => by
    cases ret with
    | none => rfl
    | some r =>
      rcases r with ⟨_, names, body, _, _⟩
      cases h with
      | none => simp only [everyStackVarHOL, everyStackVarFast, everyName_eq_fast, everyStackVar_eq_fast pred body]
      | some hv =>
        rcases hv with ⟨_, hbody, _, _⟩
        simp only [everyStackVarHOL, everyStackVarFast, everyName_eq_fast, everyStackVar_eq_fast pred body, everyStackVar_eq_fast pred hbody]
  | .skip | .move _ _ | .inst _ | .assign _ _ | .get _ _ | .store _ _
  | .codeBufferWrite _ _ | .dataBufferWrite _ _ | .locValue _ _ | .storeConsts _ _ _ _ _
  | .raise _ | .return _ _ | .tick | .set _ _ | .opCurrHeap _ _ _ | .shareInst _ _ _
  | .break _ | .continue _ => rfl

def everyEvenColourFast (colour : Spt Nat) : Bool :=
  (sptToAListFast colour).all fun (key, value) =>
    if isPhyVar key then value == key / 2 else true

theorem everyEvenColour_eq_fast (colour : Spt Nat) :
    WordAlloc.everyEvenColour colour = everyEvenColourFast colour := by
  unfold WordAlloc.everyEvenColour everyEvenColourFast
  rw [sptToAList_eq_fast]

def getClashTreeS {width : Nat} [NeZero width] :
    (prog : WordLangProgHOL (BitVec width)) → List (NumSet × NumSet) → RegAlloc.ClashTree
  | .skip, _ => .delta [] []
  | .move _ moves, _ => .delta (moves.map Prod.fst) (moves.map Prod.snd)
  | .inst instruction, _ => WordAlloc.getDeltaInst (HolInst.ofWordLangInst instruction)
  | .assign name value, _ => .delta [name] (WordAlloc.getReadsExpHOL value)
  | .get name _, _ => .delta [name] []
  | .store address value, _ => .delta [] (value :: WordAlloc.getReadsExpHOL address)
  | .seq first second, lt => .seq (getClashTreeS first lt) (getClashTreeS second lt)
  | .ite _ condition right thenBranch elseBranch, lt =>
      let thenTree := getClashTreeS thenBranch lt
      let elseTree := getClashTreeS elseBranch lt
      match right with
      | .reg register => .seq (.delta [] [condition, register]) (.branch none thenTree elseTree)
      | .imm _ => .seq (.delta [] [condition]) (.branch none thenTree elseTree)
  | .mustTerminate body, lt => getClashTreeS body lt
  | .alloc destination cutsets, _ =>
      .seq (.delta [] [destination]) (.set (sptUnionS cutsets.1 cutsets.2))
  | .install r1 r2 r3 r4 cutsets, _ =>
      .seq (.delta [] [r4, r3, r2, r1])
        (.seq (.set (sptUnionS cutsets.1 cutsets.2)) (.delta [r1] []))
  | .codeBufferWrite r1 r2, _ => .delta [] [r2, r1]
  | .dataBufferWrite r1 r2, _ => .delta [] [r2, r1]
  | .ffi _ cptr clen ptr len cutsets, _ =>
      .seq (.delta [] [cptr, clen, ptr, len]) (.set (sptUnionS cutsets.1 cutsets.2))
  | .raise num, _ => .delta [] [num]
  | .return num1 nums, _ => .delta [] (num1 :: nums)
  | .tick, _ => .delta [] []
  | .locValue r _, _ => .delta [r] []
  | .set _ value, _ => .delta [] (WordAlloc.getReadsExpHOL value)
  | .opCurrHeap _ dst src, _ => .delta [dst] [src]
  | .storeConsts a b c d _, _ => .delta [a, b, c, d] [c, d]
  | .shareInst operator name address, _ =>
      if operator = .store ∨ operator = .store8 ∨ operator = .store16 ∨ operator = .store32
      then .delta [] (name :: WordAlloc.getReadsExpHOL address)
      else .delta [name] (WordAlloc.getReadsExpHOL address)
  | .loop names body exitNames, lt =>
      .seq (.set names)
        (.seq (.set exitNames)
          (.seq (getClashTreeS body ((names, exitNames) :: lt)) (.set names)))
  | .break index, lt => .set ((lt[index]?).map Prod.snd |>.getD .ln)
  | .continue index, lt => .set ((lt[index]?).map Prod.fst |>.getD .ln)
  | .call returns _ arguments handler, lt =>
      let argsSet := WordAlloc.numsetListInsert arguments .ln
      match returns with
      | none => .set argsSet
      | some (vs, cutsets, retHandler, _, _) =>
          let cutset := sptUnionS cutsets.1 cutsets.2
          let liveSet := sptUnionS cutset argsSet
          let retTree := .seq (.set (WordAlloc.numsetListInsert vs cutset)) (getClashTreeS retHandler lt)
          match handler with
          | none => .seq (.set liveSet) retTree
          | some (v', prog, _, _) =>
              .branch (some liveSet) retTree
                (.seq (.set (sptInsert v' () cutset)) (getClashTreeS prog lt))
termination_by structural prog _ => prog

theorem getClashTreeS_eq {width : Nat} [NeZero width]
    (p : WordLangProgHOL (BitVec width)) (lt : List (NumSet × NumSet)) :
    WordAlloc.getClashTree p lt = getClashTreeS p lt := by
  induction p using (measure (sizeOf : WordLangProgHOL (BitVec width) → Nat)).wf.induction generalizing lt with
  | h p ih =>
    change ∀ q, sizeOf q < sizeOf p → ∀ lt, WordAlloc.getClashTree q lt = getClashTreeS q lt at ih
    cases p
    case seq s1 s2 =>
      simp only [WordAlloc.getClashTree, getClashTreeS]
      rw [ih s1 (by simp_wf; try decreasing_trivial), ih s2 (by simp_wf; try decreasing_trivial)]
    case ite cmp c r s1 s2 =>
      cases r <;> simp only [WordAlloc.getClashTree, getClashTreeS] <;>
        rw [ih s1 (by simp_wf; try decreasing_trivial), ih s2 (by simp_wf; try decreasing_trivial)]
    case mustTerminate s1 =>
      simp only [WordAlloc.getClashTree, getClashTreeS]
      exact ih s1 (by simp_wf; try decreasing_trivial) lt
    case loop names body exitNames =>
      simp only [WordAlloc.getClashTree, getClashTreeS]
      rw [ih body (by simp_wf; try decreasing_trivial)]
    case call ret dest args h =>
      cases ret with
      | none => simp only [WordAlloc.getClashTree, getClashTreeS]
      | some r =>
        rcases r with ⟨vs, cutsets, retH, l1, l2⟩
        cases h with
        | none =>
          simp only [WordAlloc.getClashTree, getClashTreeS, sptUnion_eq_S]
          rw [ih retH (by simp_wf; try decreasing_trivial)]
        | some hv =>
          rcases hv with ⟨v', prog, hl1, hl2⟩
          simp only [WordAlloc.getClashTree, getClashTreeS, sptUnion_eq_S]
          rw [ih retH (by simp_wf; try decreasing_trivial), ih prog (by simp_wf; try decreasing_trivial)]
    all_goals simp only [WordAlloc.getClashTree, getClashTreeS]
    all_goals try simp only [sptUnion_eq_S]

def getForcedInst {width : Nat} [NeZero width] (c : AsmConfigExact width)
    (i : WordLangInst (BitVec width)) (acc : List (Nat × Nat)) : List (Nat × Nat) :=
  match i with
  | .arith (.addCarry r1 _ r3 r4) =>
      if c.isa = .mips ∨ c.isa = .riscv then
        (if r1 = r3 then [] else [(r1, r3)]) ++
        (if r1 = r4 then [] else [(r1, r4)]) ++ acc
      else acc
  | .arith (.addOverflow r1 _ r3 _) =>
      if c.isa = .mips ∨ c.isa = .riscv then
        (if r1 = r3 then [] else [(r1, r3)]) ++ acc
      else acc
  | .arith (.subOverflow r1 _ r3 _) =>
      if c.isa = .mips ∨ c.isa = .riscv then
        (if r1 = r3 then [] else [(r1, r3)]) ++ acc
      else acc
  | .arith (.longMul r1 r2 r3 r4) =>
      if c.isa = .armv7 then
        (if r1 = r2 then [] else [(r1, r2)]) ++ acc
      else if c.isa = .armv8 ∨ c.isa = .riscv ∨ c.isa = .ag32 then
        (if r1 = r3 then [] else [(r1, r3)]) ++
        (if r1 = r4 then [] else [(r1, r4)]) ++ acc
      else acc
  | _ => acc

def getForcedS {width : Nat} [NeZero width] (c : AsmConfigExact width) :
    (prog : WordLangProgHOL (BitVec width)) → List (Nat × Nat) → List (Nat × Nat)
  | .inst i, acc => getForcedInst c i acc
  | .mustTerminate s1, acc => getForcedS c s1 acc
  | .seq s1 s2, acc => getForcedS c s1 (getForcedS c s2 acc)
  | .ite _ _ _ e2 e3, acc => getForcedS c e2 (getForcedS c e3 acc)
  | .call (some (_, _, retHandler, _, _)) _ _ h, acc =>
      match h with
      | none => getForcedS c retHandler acc
      | some (_, prog, _, _) => getForcedS c prog (getForcedS c retHandler acc)
  | .loop _ body _, acc => getForcedS c body acc
  | _, acc => acc
termination_by structural prog _ => prog

theorem getForcedS_eq {width : Nat} [NeZero width] (c : AsmConfigExact width)
    (p : WordLangProgHOL (BitVec width)) (acc : List (Nat × Nat)) :
    WordAlloc.getForced c p acc = getForcedS c p acc := by
  induction p using (measure (sizeOf : WordLangProgHOL (BitVec width) → Nat)).wf.induction generalizing acc with
  | h p ih =>
    change ∀ q, sizeOf q < sizeOf p → ∀ acc, WordAlloc.getForced c q acc = getForcedS c q acc at ih
    cases p
    case inst i =>
      cases i
      case arith a =>
        cases a <;> simp only [WordAlloc.getForced, getForcedS, getForcedInst]
      all_goals simp only [WordAlloc.getForced, getForcedS, getForcedInst]
    case seq s1 s2 =>
      simp only [WordAlloc.getForced, getForcedS]
      rw [ih s2 (by simp_wf; try decreasing_trivial), ih s1 (by simp_wf; try decreasing_trivial)]
    case ite cmp cond r e2 e3 =>
      simp only [WordAlloc.getForced, getForcedS]
      rw [ih e3 (by simp_wf; try decreasing_trivial), ih e2 (by simp_wf; try decreasing_trivial)]
    case mustTerminate s1 =>
      simp only [WordAlloc.getForced, getForcedS]
      exact ih s1 (by simp_wf; try decreasing_trivial) acc
    case loop names body exitNames =>
      simp only [WordAlloc.getForced, getForcedS]
      exact ih body (by simp_wf; try decreasing_trivial) acc
    case call ret dest args h =>
      cases ret with
      | none => simp only [WordAlloc.getForced, getForcedS]
      | some r =>
        rcases r with ⟨vs, cutsets, retH, l1, l2⟩
        cases h with
        | none =>
          simp only [WordAlloc.getForced, getForcedS]
          exact ih retH (by simp_wf; try decreasing_trivial) acc
        | some hv =>
          rcases hv with ⟨v', prog, hl1, hl2⟩
          simp only [WordAlloc.getForced, getForcedS]
          rw [ih retH (by simp_wf; try decreasing_trivial), ih prog (by simp_wf; try decreasing_trivial)]
    all_goals simp only [WordAlloc.getForced, getForcedS]

theorem wordAllocWith_oracle_fast {width : Nat} [NeZero width]
    (ra : WordToWord.RegAllocFn) (fc : Nat) (c : AsmConfigExact width) (alg k : Nat)
    (prog coloured : WordLangProgHOL (BitVec width)) (colOpt : Option (Spt Nat)) (col : Spt Nat)
    (tree : RegAlloc.ClashTree) (forced : List (Nat × Nat))
    (hOpt : colOpt = some col)
    (hTree : getClashTreeS prog [] = tree)
    (hForced : getForcedS c prog [] = forced)
    (hEven : everyEvenColourFast col = true)
    (hClash : (checkClashTreeFast (WordAlloc.totalColour col) tree .ln .ln).isSome = true)
    (hCol : applyColourFast (WordAlloc.totalColour col) prog = coloured)
    (hStack : everyStackVarFast (fun x => decide (2 * k ≤ x)) coloured = true)
    (hForcedOk : forced.all (fun (x, y) => WordAlloc.totalColour col x != WordAlloc.totalColour col y) = true) :
    WordToWord.wordAllocWith ra fc c alg k prog colOpt = coloured := by
  unfold WordToWord.wordAllocWith WordAlloc.oracleColourOk
  rw [getClashTreeS_eq, getForcedS_eq, hOpt, hTree, hForced]
  simp only [everyEvenColour_eq_fast, checkClashTree_eq_fast, applyColour_eq_fast, everyStackVar_eq_fast,
    hEven, hClash, Bool.and_self, ↓reduceIte, hCol, hStack, hForcedOk]

theorem checkClashTreeFast_seq (f : Nat → Nat) (left right : RegAlloc.ClashTree)
    (live coloured midLive midCol : NumSet) (res : Option (NumSet × NumSet))
    (hr : checkClashTreeFast f right live coloured = some (midLive, midCol))
    (hl : checkClashTreeFast f left midLive midCol = res) :
    checkClashTreeFast f (.seq left right) live coloured = res := by
  simp only [checkClashTreeFast, hr, hl]

theorem checkClashTreeFast_branch_none (f : Nat → Nat) (left right : RegAlloc.ClashTree)
    (live coloured lOut lCol rOut rCol : NumSet) (res : Option (NumSet × NumSet))
    (hl : checkClashTreeFast f left live coloured = some (lOut, lCol))
    (hr : checkClashTreeFast f right live coloured = some (rOut, rCol))
    (hm : RegAlloc.checkPartialCol f ((sptToAListFast (sptDifferenceS rOut lOut)).map Prod.fst) lOut lCol = res) :
    checkClashTreeFast f (.branch none left right) live coloured = res := by
  simp only [checkClashTreeFast, hl, hr, hm]

open Lean Meta Elab Command in
private partial def countClashNodes (e : Expr) : Nat :=
  if e.isAppOfArity ``RegAlloc.ClashTree.seq 2 then
    let args := e.getAppArgs
    1 + countClashNodes args[0]! + countClashNodes args[1]!
  else if e.isAppOfArity ``RegAlloc.ClashTree.branch 3 then
    let args := e.getAppArgs
    1 + countClashNodes args[1]! + countClashNodes args[2]!
  else 1

open Lean Meta Elab Command in
private def kernelEvalStep (stem : Name) (lhs : Expr) : MetaM (Expr × Expr) := do
  let rhs ← withTransparency .all <| reduce lhs (explicitOnly := false) (skipTypes := true) (skipProofs := true)
  let rhs ← Sym.SymM.run <| Sym.shareCommon rhs
  let eqName ← mkFreshUserName ((← getCurrNamespace) ++ stem)
  let eqType ← mkEq lhs rhs
  let rflProof ← mkEqRefl rhs
  addDecl (.thmDecl { name := eqName, levelParams := [], type := eqType, value := rflProof })
  return (rhs, mkConst eqName)

open Lean Meta Elab Command in
private def sealStep (stem : Name) (prf : Expr) : MetaM Expr := do
  let eqName ← mkFreshUserName ((← getCurrNamespace) ++ stem)
  let eqType ← inferType prf
  addDecl (.thmDecl { name := eqName, levelParams := [], type := eqType, value := prf })
  return mkConst eqName

open Lean Meta Elab Command in
private partial def solveCheckClashFast (fExpr tree live col : Expr) : MetaM (Expr × Expr) := do
  if countClashNodes tree > 100 then
    if tree.isAppOfArity ``RegAlloc.ClashTree.seq 2 then
      let args := tree.getAppArgs
      let left := args[0]!
      let right := args[1]!
      let (rRes, hr) ← solveCheckClashFast fExpr right live col
      let pArgs := (rRes.getAppArgs[1]!).getAppArgs
      let midLive := pArgs[2]!
      let midCol := pArgs[3]!
      let (lRes, hl) ← solveCheckClashFast fExpr left midLive midCol
      let prf ← mkAppM ``checkClashTreeFast_seq #[fExpr, left, right, live, col, midLive, midCol, lRes, hr, hl]
      return (lRes, ← sealStep `clashSeq prf)
    else if tree.isAppOfArity ``RegAlloc.ClashTree.branch 3 then
      let args := tree.getAppArgs
      if args[0]!.isAppOfArity ``Option.none 1 then
        let left := args[1]!
        let right := args[2]!
        let (lRes, hl) ← solveCheckClashFast fExpr left live col
        let (rRes, hr) ← solveCheckClashFast fExpr right live col
        let lpArgs := (lRes.getAppArgs[1]!).getAppArgs
        let lOut := lpArgs[2]!
        let lCol := lpArgs[3]!
        let rpArgs := (rRes.getAppArgs[1]!).getAppArgs
        let rOut := rpArgs[2]!
        let rCol := rpArgs[3]!
        let fstFn ← mkAppOptM ``Prod.fst #[some (mkConst ``Nat), some (mkConst ``Unit)]
        let mergeLhs ← mkAppM ``RegAlloc.checkPartialCol #[
          fExpr,
          ← mkAppM ``List.map #[fstFn, ← mkAppM ``sptToAListFast #[← mkAppM ``sptDifferenceS #[rOut, lOut]]],
          lOut, lCol]
        let (mRes, hm) ← kernelEvalStep `clashMerge mergeLhs
        let prf ← mkAppM ``checkClashTreeFast_branch_none #[fExpr, left, right, live, col, lOut, lCol, rOut, rCol, mRes, hl, hr, hm]
        return (mRes, ← sealStep `clashBr prf)
      else
        kernelEvalStep `clashLeaf (← mkAppM ``checkClashTreeFast #[fExpr, tree, live, col])
    else
      kernelEvalStep `clashLeaf (← mkAppM ``checkClashTreeFast #[fExpr, tree, live, col])
  else
    kernelEvalStep `clashLeaf (← mkAppM ``checkClashTreeFast #[fExpr, tree, live, col])

open Lean Meta Elab Command in
elab "wave8_certify_clash " id:ident " := " fT:term " on " treeT:term : command => do
  liftTermElabM do
    let fExpr ← Term.elabTerm fT none
    let treeConst ← Term.elabTerm treeT none
    Term.synthesizeSyntheticMVarsNoPostponing
    let fExpr ← instantiateMVars fExpr
    let treeConst ← instantiateMVars treeConst
    let some treeBody ← withTransparency .all (unfoldDefinition? treeConst)
      | throwError "expected constant tree"
    let lnExpr ← Term.elabTerm (← `((.ln : NumSet))) none
    let (_, hBody) ← solveCheckClashFast fExpr treeBody lnExpr lnExpr
    let lhsFull ← mkAppM ``Option.isSome #[← mkAppM ``checkClashTreeFast #[fExpr, treeConst, lnExpr, lnExpr]]
    let hUnfold : Expr ← mkEqRefl lhsFull
    let isSomeFn ← mkAppOptM ``Option.isSome #[some (← mkAppM ``Prod #[mkConst ``NumSet, mkConst ``NumSet])]
    let hIsSome ← mkAppM ``congrArg #[isSomeFn, hBody]
    let (_, hTrue) ← kernelEvalStep `clashIsSome (← mkAppM ``Option.isSome #[(← inferType hBody).getAppArgs[2]!])
    let fullPrf ← mkEqTrans hUnfold (← mkEqTrans hIsSome hTrue)
    let currNs ← getCurrNamespace
    let eqName := currNs ++ Name.mkSimple (id.getId.toString ++ "_eq")
    addDecl (.thmDecl { name := eqName, levelParams := [], type := ← inferType fullPrf, value := fullPrf })

end InitECandidate.Solver.Wave8Stage
