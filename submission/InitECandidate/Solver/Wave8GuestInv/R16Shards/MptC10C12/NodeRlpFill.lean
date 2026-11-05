import InitECandidate.Solver.Wave8GuestInv.ContractParts.C10
import InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12.BuildMptIndexed

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-- `keccak_pad` (136 B) and `keccak_st` (200 B) are allocated (when nonzero) and disjoint
from `Nd`'s node records and paths. Propagated from `MptObjReady` in `mpt_root`. -/
def KeccakBufsSafe {F : Type} (s : PanSemStateFiniteExact 64 F) (Nd : List Nat) : Prop :=
  ∀ gs ∈ ([("keccak_pad", 136), ("keccak_st", 200)] : List (String × Nat)),
    ((bufferRegion s gs).2 = 0 ∨ Allocated s (bufferRegion s gs)) ∧
      ∀ o ∈ nodeExtents s Nd, Disj o (bufferRegion s gs)

/-- Strengthened `NodeRlpReady` carrying `KeccakBufsSafe` for the witnessing `Nd`. -/
def NodeRlpReadyK : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ ∃ Nd, NodeHeap s Nd ∧ RootIn Nd (locN s "node") ∧ KeccakBufsSafe s Nd

/-- The non-null node guard exported by `node_rlp` and `node_hash`. -/
def NodeRlpReadyNonNull : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => NodeRlpReadyK s ∧ locN s "node" ≠ 0

/-- The guard needed by `_node_rlp_fill`: a typed, non-null node with a nonzero kind. -/
def NodeRlpReadyStrong : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => NodeRlpReadyK s ∧ locN s "node" ≠ 0 ∧ memW s (locN s "node") ≠ 0

namespace NodeRlpFillProof

private theorem node_mem_ne_zero {F : Type} {s : PanSemStateFiniteExact 64 F}
    {Nd : List Nat} {n : Nat} (hNd : NodeHeap s Nd) (hn : n ∈ Nd) : n ≠ 0 := by
  have hbase : sourceBase ≤ n := (hNd.1 n hn).2.2.1.1
  have hpos : 0 < sourceBase := by decide
  omega

private theorem strong_to_nonNull {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : NodeRlpReadyStrong s) : NodeRlpReadyNonNull s := ⟨h.1, h.2.1⟩

private theorem strong_kind_bounds {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : NodeRlpReadyStrong s) :
    1 ≤ memW s (locN s "node") ∧ memW s (locN s "node") ≤ 3 := by
  obtain ⟨Nd, hNd, hr, _⟩ := h.1.2
  have hn : locN s "node" ∈ Nd := hr.resolve_left h.2.1
  exact ⟨Nat.pos_of_ne_zero h.2.2, (hNd.1 _ hn).1⟩

private theorem keccakBufsSafe_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) {Nd : List Nat}
    (h : KeccakBufsSafe s Nd) :
    KeccakBufsSafe { s with locals := locals, clock := k } Nd := h

private theorem localsOnlyNonNull : LocalsOnly ["node"] NodeRlpReadyNonNull := by
  intro F s locals k hl hP
  have ht := locN_congr s locals k "node" (hl "node" (by simp))
  simp only [NodeRlpReadyNonNull, NodeRlpReadyK, arenaReady_with_locals] at hP ⊢
  rw [ht]
  exact hP

private theorem localsOnlyStrong : LocalsOnly ["node"] NodeRlpReadyStrong := by
  intro F s locals k hl hP
  have ht := locN_congr s locals k "node" (hl "node" (by simp))
  simp only [NodeRlpReadyStrong, NodeRlpReadyK, arenaReady_with_locals] at hP ⊢
  rw [ht]
  exact hP

private theorem entryNonNull {fname : MlS}
    {e : List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL}
    (hl : originalRuntimeCode.lookup fname = some e)
    (hp : e.1 = [(ofString "node", .one)]) :
    CallEntryOn NodeRlpReadyNonNull NodeRlpReadyNonNull fname
      [.var .local (ofString "node")] := by
  obtain ⟨ps, b, r⟩ := e
  dsimp only at hp
  subst hp
  intro F state values body' callee ret' hcode hP hargs hlook
  have hc := callee_param_one state fname (ofString "node") .one b r
    (by rw [hcode]; exact hl) values body' callee ret' hargs hlook
  exact localsOnlyNonNull state callee (state.clock - 1) (by simpa using hc) hP

private theorem entryStrong {fname : MlS}
    {e : List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL}
    (hl : originalRuntimeCode.lookup fname = some e)
    (hp : e.1 = [(ofString "node", .one)]) :
    CallEntryOn NodeRlpReadyStrong NodeRlpReadyStrong fname
      [.var .local (ofString "node")] := by
  obtain ⟨ps, b, r⟩ := e
  dsimp only at hp
  subst hp
  intro F state values body' callee ret' hcode hP hargs hlook
  have hc := callee_param_one state fname (ofString "node") .one b r
    (by rw [hcode]; exact hl) values body' callee ret' hargs hlook
  exact localsOnlyStrong state callee (state.clock - 1) (by simpa using hc) hP

private theorem straight (p : ProgHOL 64) (h : extStraightLine p = true) :
    TerminatingProgBoundedOn GuestInv p 0 :=
  fun s hc _ => TerminatingProgBounded.straight p h s hc

private theorem weakenGuard {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {p : ProgHOL 64} {k : Nat} (h : TerminatingProgBoundedOn Q p k)
    (hp : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → Q s) :
    TerminatingProgBoundedOn P p k := fun s hc hP => h s hc (hp s hP)

private theorem seq_hoare_to {P R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {first second : ProgHOL 64} {a b : Nat}
    (h1 : TerminatingProgBoundedOn P first a)
    (hp : Hoare P first (fun r t => r = none → R t))
    (h2 : TerminatingProgBoundedOn R second b) :
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

private theorem cond_eq_false {F : Type} {s : PanSemStateFiniteExact 64 F}
    {e : ExpHOL 64} {k : BitVec 64}
    (h : CondFalse (.cmp .equal e (.const k)) s) :
    ∃ w : BitVec 64, evalAt s e = some (.val (.word w)) ∧ w ≠ k := by
  obtain ⟨a, b, ha, hb, hz⟩ := evalAt_cmp s .equal e (.const k) 0 h
  cases evalAt_const s k _ hb
  refine ⟨a, ha, ?_⟩
  intro hab
  simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hab] at hz

private theorem cond_local_eq_false {F : Type} {s : PanSemStateFiniteExact 64 F}
    {n : String} {k : BitVec 64}
    (h : CondFalse (.cmp .equal (.var .local (ofString n)) (.const k)) s) :
    locN s n ≠ k.toNat := by
  obtain ⟨w, hw, hn⟩ := cond_eq_false h
  rw [← evalAt_local s n w hw]
  exact fun he => hn (BitVec.eq_of_toNat_eq he)

private theorem evalAt_loadL' {F : Type} (t : PanSemStateFiniteExact 64 F)
    (g : String) (k a : BitVec 64)
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

private theorem evalAt_loadL {F : Type} (t : PanSemStateFiniteExact 64 F)
    (g : String) (k : BitVec 64) (v : ValueHOL 64)
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

private theorem strong_of_kind_cond_false {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hs : NodeRlpReadyNonNull s)
    (hc : CondFalse (.cmp .equal
      (.load .one (.op .add [.var .local (ofString "node"), .const 0])) (.const 0)) s) :
    NodeRlpReadyStrong s := by
  refine ⟨hs.1, hs.2, ?_⟩
  obtain ⟨w, hw, hne⟩ := cond_eq_false hc
  have hm : w.toNat = memW s (locN s "node") := by
    simpa using evalAt_loadL' s "node" 0 w hw
  intro hz
  apply hne
  apply BitVec.eq_of_toNat_eq
  have hwz : w.toNat = (0 : BitVec 64).toNat := by
    rw [hm]
    simpa using hz
  exact hwz

private theorem lookup_fill : originalRuntimeCode.lookup (ofString "_node_rlp_fill") =
    some ((sourceFunctionEntry Guest.Software.guestFn__node_rlp_fill).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 284 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn__node_rlp_fill) rfl

private theorem lookup_rlp : originalRuntimeCode.lookup (ofString "node_rlp") =
    some ((sourceFunctionEntry Guest.Software.guestFn_node_rlp).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 285 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_node_rlp) rfl

private theorem lookup_hash : originalRuntimeCode.lookup (ofString "node_hash") =
    some ((sourceFunctionEntry Guest.Software.guestFn_node_hash).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 290 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_node_hash) rfl

private theorem lookup_root : originalRuntimeCode.lookup (ofString "mpt_root") =
    some ((sourceFunctionEntry Guest.Software.guestFn_mpt_root).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 291 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_mpt_root) rfl

private theorem lookup_mpt_fail :
    originalRuntimeCode.lookup (ofString "mpt_fail") =
      some ([(ofString "code", .one)], sourceFnBody Guest.Software.guestFn_mpt_fail, .one) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 246 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_mpt_fail) rfl

private theorem eval_call_mpt_fail_no_none_no_ret {F : Type}
    (s : PanSemStateFiniteExact 64 F) (c : BitVec 64) (hc : s.code = originalRuntimeCode) :
    let out := evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "mpt_fail") [.const c])
    out.1 ≠ none ∧ (∀ v, out.1 ≠ some (.returned v)) := by
  dsimp only
  rw [evaluateHOLFiniteState_call]
  have hargs : evalListHOLFinite s
      (h := fun a => Classical.propDecidable (s.memaddrs a)) [.const c] =
      some [.val (.word c)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact]
  have hlk := pan_one_word_lookup s.code.lookup (ofString "mpt_fail") (ofString "code")
    (sourceFnBody Guest.Software.guestFn_mpt_fail) c (by rw [hc]; exact lookup_mpt_fail)
  rw [hargs]
  dsimp only
  rw [hlk]
  dsimp only
  split
  · exact ⟨by simp, fun _ => by simp⟩
  · have hb : sourceFnBody Guest.Software.guestFn_mpt_fail =
        .seq (.raise (ofString "MptErr") (.var .local (ofString "code"))) (.return (.const 0)) := rfl
    have hraise_out : ∀ st : PanSemStateFiniteExact 64 F,
        let ro := (evaluateHOLFiniteState st
          (.raise (ofString "MptErr") (.var .local (ofString "code")))).1
        ro = some .error ∨ ∃ ev, ro = some (.exception (ofString "MptErr") ev) := by
      intro st
      dsimp only
      rw [evaluateHOLFiniteState_raise]
      split
      · dsimp only
        split <;> simp
      · simp
    let entry := callEntryStateHOLFinite s
      (HolFiniteMapExact.empty.update (ofString "code", .val (.word c)))
    rcases hbody : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_mpt_fail) with
      ⟨res, st⟩
    have hr := hraise_out entry
    rw [hb, evaluateHOLFiniteState_seq_line780] at hbody
    rcases hr_st : evaluateHOLFiniteState entry
      (.raise (ofString "MptErr") (.var .local (ofString "code"))) with ⟨rr, sr⟩
    rw [hr_st] at hr hbody
    dsimp only at hr hbody
    rcases hr with rfl | ⟨ev, rfl⟩
    · injection hbody with h1 _
      subst h1
      exact ⟨by simp, fun _ => by simp⟩
    · injection hbody with h1 _
      subst h1
      exact ⟨by simp, fun _ => by simp⟩

private theorem mpt_fail_hoare {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} :
    Hoare P (.call (some (none, none)) (ofString "mpt_fail") [.const 2])
      (fun r t => r = none → NodeRlpReadyStrong t) := by
  refine ⟨fun {F} s hc _ _ => ?_⟩
  have hno := (eval_call_mpt_fail_no_none_no_ret s 2 hc).1
  exact fun hn => (hno hn).elim

end NodeRlpFillProof

/-- Strengthened `node_rlp`: its explicit kind check justifies the strong fill guard. -/
theorem gbody_node_rlp_strong
    (hf : TerminatingFunBoundedOn NodeRlpReadyStrong
      (ofString "_node_rlp_fill") K.«_node_rlp_fill»)
    (hm : TerminatingFunBoundedOn GuestInv (ofString "mpt_fail") K.«mpt_fail»)
    (_hr : ReadOnlyFn (ofString "mpt_fail")) :
    TerminatingFunBoundedOn NodeRlpReadyNonNull (ofString "node_rlp") K.«node_rlp» := by
  refine ⟨_, _, _, NodeRlpFillProof.lookup_rlp, ?_⟩
  simp only [sourceFunctionEntry, Guest.Software.guestFn_node_rlp,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.dec_onLocals NodeRlpFillProof.localsOnlyNonNull _ (by decide) _ _
      (TerminatingProgBoundedOn.seq_hoare
        (NodeRlpFillProof.weakenGuard (NodeRlpFillProof.straight _ rfl) (fun s h => h.1.1.1))
        (Hoare.ite_return_skip _ _)
        (NodeRlpFillProof.seq_hoare_to
          (TerminatingProgBoundedOn.ite_on
            (TerminatingProgBoundedOn.call_on hm _ _
              (callEntryOn_of_imp localsFree_guestInv (fun s h => h.1.1.1) _ _))
            (NodeRlpFillProof.weakenGuard (NodeRlpFillProof.straight _ rfl) (fun s h => h.1.1.1)))
          (Hoare.ite
            (Hoare.mono NodeRlpFillProof.mpt_fail_hoare (fun s h => h.1))
            (Hoare.skip (fun s h _ => NodeRlpFillProof.strong_of_kind_cond_false h.1 h.2))
            (fun _ _ h => absurd h (by simp)))
          (TerminatingProgBoundedOn.seq_guestInv_after
            (TerminatingProgBoundedOn.call_on hf _ _
              (NodeRlpFillProof.entryStrong NodeRlpFillProof.lookup_fill (by rfl)))
            (fun s h => h.1.1.1)
            (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))))) ?_
  unfold K.«node_rlp»
  simp only [Nat.max_def]
  split <;> omega

/-- Strengthened `node_hash`, retaining the non-null guard across its `node_rlp` call. -/
theorem gbody_node_hash_strong
    (ha : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (hk : TerminatingFunBoundedOn GuestInv (ofString "keccak256") K.«keccak256»)
    (hn : TerminatingFunBoundedOn NodeRlpReadyNonNull (ofString "node_rlp") K.«node_rlp») :
    TerminatingFunBoundedOn NodeRlpReadyNonNull (ofString "node_hash") K.«node_hash» := by
  refine ⟨_, _, _, NodeRlpFillProof.lookup_hash, ?_⟩
  simp only [sourceFunctionEntry, Guest.Software.guestFn_node_hash,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.dec_onLocals NodeRlpFillProof.localsOnlyNonNull _ (by decide) _ _
      (TerminatingProgBoundedOn.seq_hoare
        (NodeRlpFillProof.weakenGuard (NodeRlpFillProof.straight _ rfl) (fun s h => h.1.1.1))
        (Hoare.ite_return_skip _ _)
        (TerminatingProgBoundedOn.decCall_on hn _ _ _
          (NodeRlpFillProof.entryNonNull NodeRlpFillProof.lookup_rlp (by rfl))
          (decCallResumeOn_guestInv (fun s h => h.1.1.1) _ _ _)
          (TerminatingProgBoundedOn.decCall_guestInv ha _ _ _
            (TerminatingProgBoundedOn.seq_guestInv
              (TerminatingProgBoundedOn.call_guestInv hk _ _)
              (TerminatingProgBoundedOn.seq_guestInv (NodeRlpFillProof.straight _ rfl)
                (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))))))) ?_
  unfold K.«node_hash»
  omega

namespace NodeRlpFillProof

private theorem callee_param_alias {F : Type} (state : PanSemStateFiniteExact 64 F)
    (fname pk caller : MlS) (sk : ShapeHOL) (body : ProgHOL 64) (ret : ShapeHOL)
    (hl : state.code.lookup fname = some ([(pk, sk)], body, ret))
    (values : List (ValueHOL 64)) (body' : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL)
    (hargs : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local caller] = some values)
    (hlook : lookupCodeHOLFinite state.code.lookup fname values = some (body', callee, ret')) :
    callee.lookup pk = state.locals.lookup caller := by
  rw [evalListHOLFinite_eq_toExact] at hargs
  simp only [evalListHOLExact, evalHOLExact] at hargs
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hlook
  split at hlook
  · cases hlook
  · rename_i exactBody exactLocals exactShape raw
    have heq := Option.some.inj hlook
    rcases Prod.mk.inj heq with ⟨rfl, hrest⟩
    rcases Prod.mk.inj hrest with ⟨rfl, _⟩
    unfold lookupCodeHOLExact at raw
    rw [hl] at raw
    dsimp only at raw
    rcases hv : state.locals.lookup caller with _ | v
    · rw [hv] at hargs
      cases hargs
    · rw [hv] at hargs
      cases hargs
      split at raw
      · have rawEq := Option.some.inj raw
        rcases Prod.mk.inj rawEq with ⟨-, hrest2⟩
        rcases Prod.mk.inj hrest2 with ⟨hloc, -⟩
        subst hloc
        simp
      · cases raw

private theorem dec_guard {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (name : MlS) (shape : ShapeHOL) (init : ExpHOL 64) {body : ProgHOL 64} {k : Nat}
    (hi : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
      P s → evalAt s init = some v → Q (setVarHOLFinite name v s))
    (hb : TerminatingProgBoundedOn Q body k) :
    TerminatingProgBoundedOn P (.dec name shape init body) k := by
  intro F s hc hP hnt
  rw [evaluateHOLFiniteState_dec_total] at hnt ⊢
  dsimp only at hnt ⊢
  revert hnt
  split <;> intro hnt
  · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  · rename_i v hv
    revert hnt
    split <;> intro hnt
    · have h := hb (setVarHOLFinite name v s) hc (hi s v hP hv) hnt
      simpa only [setVarHOLFinite] using h
    · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩

private def RootReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ ∃ Nd, NodeHeap s Nd ∧ RootIn Nd (locN s "root") ∧ KeccakBufsSafe s Nd

private def RootCallReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => RootReady s ∧ locN s "root" ≠ 0

private theorem root_init {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (hs : MptObjReady s)
    (hv : evalAt s (.load .one (.op .add [.var .local (ofString "m"), .const 0])) = some v) :
    RootReady (setVarHOLFinite (ofString "root") v s) := by
  obtain ⟨w, rfl, hw⟩ := evalAt_loadL s "m" 0 v hv
  obtain ⟨ha, S, hS, ⟨Nd, hm⟩, _rest⟩ := hs
  refine ⟨localsFree_arenaReady s _ _ ha, Nd, hm.2.2.2.2.1, ?_, ?_⟩
  · rw [locN_setVar_same, hw]
    simpa using hm.2.2.2.2.2.1
  · intro gs hgs
    have hj_fix : bufferRegion s gs ∈ fixedObjects s := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hgs
      have hbuf : bufferRegion s gs ∈ globalBuffers.map (bufferRegion s) := by
        rcases hgs with rfl | rfl
        · exact List.mem_map.mpr ⟨("keccak_pad", 136), by decide, rfl⟩
        · exact List.mem_map.mpr ⟨("keccak_st", 200), by decide, rfl⟩
      simp only [fixedObjects, List.mem_append, bufferRegion] at hbuf ⊢
      exact Or.inl (Or.inl (Or.inl hbuf))
    refine ⟨?_, fun o ho => (hm.2.2.2.2.2.2 o ho).2.2 _ hj_fix⟩
    rcases hS.2.2.1.1 (bufferRegion s gs) hj_fix with hz | ⟨hal, _⟩
    · exact Or.inl hz
    · exact Or.inr hal

private theorem root_call_of_false {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hs : RootReady s)
    (hc : CondFalse (.cmp .equal (.var .local (ofString "root")) (.const 0)) s) :
    RootCallReady s := ⟨hs, cond_local_eq_false hc⟩

private theorem root_entry :
    CallEntryOn RootCallReady NodeRlpReadyNonNull (ofString "node_hash")
      [.var .local (ofString "root")] := by
  intro F s vs b callee r hc hP hargs hl
  have hp := callee_param_alias s (ofString "node_hash") (ofString "node") (ofString "root")
    .one _ _ (by rw [hc]; exact lookup_hash) vs b callee r hargs hl
  have hx : locN (callEntryStateHOLFinite s callee) "node" = locN s "root" := by
    simp only [locN, callEntryStateHOLFinite, hp]
  refine ⟨⟨localsFree_arenaReady s _ _ hP.1.1, ?_⟩, ?_⟩
  · rw [hx]
    exact hP.1.2
  · rw [hx]
    exact hP.2

end NodeRlpFillProof

/-- Strengthened `mpt_root`; the original external `MptObjReady` conclusion is unchanged. -/
theorem gbody_mpt_root_strong
    (hm : TerminatingFunBoundedOn GuestInv (ofString "memcpy") K.«memcpy»)
    (hn : TerminatingFunBoundedOn NodeRlpReadyNonNull (ofString "node_hash") K.«node_hash») :
    TerminatingFunBoundedOn MptObjReady (ofString "mpt_root") K.«mpt_root» := by
  refine ⟨_, _, _, NodeRlpFillProof.lookup_root, ?_⟩
  simp only [sourceFunctionEntry, Guest.Software.guestFn_mpt_root,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (NodeRlpFillProof.dec_guard _ _ _ NodeRlpFillProof.root_init
      (NodeRlpFillProof.seq_hoare_to
        (TerminatingProgBoundedOn.ite_on
          (NodeRlpFillProof.weakenGuard
            (TerminatingProgBoundedOn.seq_guestInv
              (TerminatingProgBoundedOn.call_guestInv hm _ _)
              (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))
            (fun s h => h.1.1))
          (NodeRlpFillProof.weakenGuard (NodeRlpFillProof.straight _ rfl) (fun s h => h.1.1)))
        (Hoare.ite
          ⟨fun s hc hP hnt he => by
            rw [evaluateHOLFiniteState_seq_line780] at he
            dsimp only at he
            split at he
            · exact False.elim (return_ne_none _ _ he)
            · simp_all⟩
          (Hoare.skip (fun s h _ => NodeRlpFillProof.root_call_of_false h.1 h.2))
          (fun _ _ h => absurd h (by simp)))
        (TerminatingProgBoundedOn.decCall_on hn _ _ _ NodeRlpFillProof.root_entry
          (decCallResumeOn_guestInv (fun s h => h.1.1.1) _ _ _)
          (TerminatingProgBoundedOn.seq_guestInv
            (TerminatingProgBoundedOn.call_guestInv hm _ _)
            (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))))) ?_
  unfold K.«mpt_root»
  simp only [Nat.max_def]
  split <;> omega

end InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12
