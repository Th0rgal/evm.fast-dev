import InitECandidate.Solver.Wave8GuestInv.MemoryViews
import InitECandidate.Solver.GuestTrapOutcomes
import Guest.SoftwareAst

/-! `nf_node_invalidate`: `node_invalidate(nd)` preserves typed node heaps (`NodeFn ["nd"]`).
At `nd = 0`, `store(nd + 8, 0)` errors (`8 ∉ ordinaryDomain`) and cannot resume; otherwise
`nd ∈ Nd`, so `node_invalidate` only zeroes the cache words `nd+8/+16/+24` inside `nodeIvl s nd`,
leaving all node kinds (`+0`), paths (`+32/+40`), children (`+32..+160`), and nibble bytes intact.
Checked against frozen spec revision 9 (`8a79d9f28`, tag `wave8-spec-frozen-r9`). -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace InitECandidate.Solver.Wave8Contracts.M25

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

def FunSpec_ni (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
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

def Resumes_ni (r : Option (PanSemResultExact 64)) : Prop :=
  (∃ v, r = some (.returned v)) ∨ ∃ e v, r = some (.exception e v) ∧ e ≠ ofString "TrapErr"

def NodeArgs_ni (names : List String)
    (req : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Nat → Prop) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ ∃ Nd, NodeHeap s Nd ∧ (∀ n ∈ names, RootIn Nd (locN s n)) ∧ req s Nd

def NodeFnExit_ni (names : List String)
    (req : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Nat → Prop) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F →
    Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop :=
  fun s r post => Resumes_ni r → ArenaReady post ∧ globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
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

def NodeFn_ni (names : List String)
    (req : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Nat → Prop) (fname : MlS) : Prop :=
  FunSpec_ni (NodeArgs_ni names req) (NodeFnExit_ni names req) fname

private theorem lookup_node_invalidate :
    originalRuntimeCode.lookup (ofString "node_invalidate") =
      some ([(ofString "nd", .one)],
        .seq (.store (.op .add [.var .local (ofString "nd"), .const 8]) (.const 0))
          (.seq (.store (.op .add [.var .local (ofString "nd"), .const 16]) (.const 0))
            (.seq (.store (.op .add [.var .local (ofString "nd"), .const 24]) (.const 0))
              (.return (.const 0)))), .one) :=
  lookup_of_guestAst_getElem 259 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_node_invalidate) rfl

private theorem not_resumes_error : ¬ Resumes_ni (some (.error : PanSemResultExact 64)) := by
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h

private theorem addresses_ge_base (base : BitVec 64) (n : Nat) (x : BitVec 64)
    (hfit : base.toNat + 8 * n < 2 ^ 64)
    (h : Flapjack.Compiler.Backend.StackRemove.addresses base n x) :
    base.toNat ≤ x.toNat := by
  induction n generalizing base with
  | zero => exact absurd h id
  | succ n ih =>
    rcases h with h | h
    · subst h; omega
    · have hb : (base + Flapjack.Compiler.Backend.StackRemove.bytesInWord 64).toNat = base.toNat + 8 := by
        rw [BitVec.toNat_add_of_lt]
        · simp [Flapjack.Compiler.Backend.StackRemove.bytesInWord]
        · simp [Flapjack.Compiler.Backend.StackRemove.bytesInWord]; omega
      have := ih (base + Flapjack.Compiler.Backend.StackRemove.bytesInWord 64) (by omega) h
      omega

private theorem ordinaryDomain_ge_sourceBase (x : BitVec 64) (h : ordinaryDomain x) :
    sourceBase ≤ x.toNat := by
  unfold ordinaryDomain at h
  have hn : ((stackStart - sourceBase) / 8 - globalsWords) = 3888119741 := by decide
  rw [hn] at h
  have hs : (BitVec.ofNat 64 sourceBase).toNat = 2701131776 := by decide
  have hge := addresses_ge_base _ _ x (by rw [hs]; decide) h
  rw [hs] at hge
  have e1 : sourceBase = 2701131776 := by decide
  omega

private theorem eval_store_const_zero {F : Type} (s : PanSemStateFiniteExact 64 F)
    (nd : BitVec 64) (hnd : s.locals.lookup (ofString "nd") = some (.val (.word nd)))
    (off : BitVec 64) :
    (¬ s.memaddrs (nd + off) ∧
      evaluateHOLFiniteState s (.store (.op .add [.var .local (ofString "nd"), .const off]) (.const 0)) =
        (some .error, s)) ∨
    (s.memaddrs (nd + off) ∧
      evaluateHOLFiniteState s (.store (.op .add [.var .local (ofString "nd"), .const off]) (.const 0)) =
        (none, { s with memory := fun a => if a = nd + off then .word 0 else s.memory a })) := by
  rw [evaluateHOLFiniteState_store]
  have hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local (ofString "nd"), .const off]) = some (.val (.word (nd + off))) := by
    simp [evalHOLExact, evalListHOLExact, hnd, valueIsWord, valueWord, wordOpHOL, wordOp]
  have hsrc : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.const 0) = some (.val (.word 0)) := rfl
  rw [hdst, hsrc]
  simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL]
  by_cases hdom : s.memaddrs (nd + off)
  · right; exact ⟨hdom, by simp [hdom]⟩
  · left; exact ⟨hdom, by simp [hdom]⟩

private theorem nodeSize_bounds (k : Nat) : 32 ≤ nodeSize k ∧ nodeSize k ≤ 176 := by
  unfold nodeSize
  split <;> try omega
  split <;> try omega
  split <;> omega

private theorem byteAlign_bounds (a : Nat) (ha : a < 2 ^ 64) :
    (panByteAlignHOL (BitVec.ofNat 64 a)).toNat ≤ a ∧
      a < (panByteAlignHOL (BitVec.ofNat 64 a)).toNat + 8 := by
  have h8 : 2 ^ Nat.log2 (64 / 8) = 8 := by decide
  simp only [panByteAlignHOL, h8, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]
  have hlt : a / 8 * 8 < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hlt]
  omega

/-- `node_invalidate` (AST line 10061): typed nodes in, typed nodes out (MPT tier); requirement: none. -/
theorem «nf_node_invalidate» :
    NodeFn_ni ["nd"]
    (fun _ _ => True)
    (ofString "node_invalidate") := by
  refine ⟨_, _, _, lookup_node_invalidate, ?_⟩
  intro F s _hcode hP _ _hnt hres
  rcases hP with ⟨⟨hginv, harena⟩, _⟩
  rcases hnd : s.locals.lookup (ofString "nd") with _ | vnd
  · rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_store] at hres
    simp [evalHOLExact, evalListHOLExact, hnd] at hres
    exact absurd hres not_resumes_error
  · rcases vnd with ⟨⟨nd⟩⟩ | fs | ⟨nm, fs⟩
    · have hloc : locN s "nd" = nd.toNat := by simp [locN, hnd]
      rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
      rcases eval_store_const_zero s nd hnd 8 with ⟨_, h1⟩ | ⟨hdom8, h1⟩
      · rw [h1] at hres; exact absurd hres not_resumes_error
      · rw [h1] at hres ⊢
        dsimp only at hres ⊢
        set s1 : PanSemStateFiniteExact 64 F :=
          { s with memory := fun a => if a = nd + 8 then .word 0 else s.memory a }
        rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
        rcases eval_store_const_zero s1 nd (by simp [s1, hnd]) 16 with ⟨_, h2⟩ | ⟨hdom16, h2⟩
        · rw [h2] at hres; exact absurd hres not_resumes_error
        · rw [h2] at hres ⊢
          dsimp only at hres ⊢
          set s2 : PanSemStateFiniteExact 64 F :=
            { s1 with memory := fun a => if a = nd + 16 then .word 0 else s1.memory a }
          rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
          rcases eval_store_const_zero s2 nd (by simp [s2, s1, hnd]) 24 with ⟨_, h3⟩ | ⟨hdom24, h3⟩
          · rw [h3] at hres; exact absurd hres not_resumes_error
          · rw [h3] at hres ⊢
            dsimp only at hres ⊢
            set s3 : PanSemStateFiniteExact 64 F :=
              { s2 with memory := fun a => if a = nd + 24 then .word 0 else s2.memory a }
            rw [evaluateHOLFiniteState_return] at hres ⊢
            have hret : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
                (.const 0) = some (.val (.word 0)) := rfl
            rw [hret] at hres ⊢
            dsimp only at hres ⊢
            have hsz : sizeOfShapeWithContextHOL s3.structs (shapeOfHOLExact (ValueHOL.val (HolWordLab.word (0 : BitVec 64)))) ≤ 32 := by
              simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
            rw [if_pos hsz] at hres ⊢
            dsimp only at hres ⊢
            set post := emptyLocalsHOLFinite s3
            -- `nd` cannot be 0 because `nd + 8 ∈ ordinaryDomain` implies `(nd + 8).toNat ≥ sourceBase`
            have hnd_ne0 : nd.toNat ≠ 0 := by
              intro hz
              have hnd0 : nd = 0 := BitVec.eq_of_toNat_eq hz
              subst hnd0
              rw [hginv.memaddrs] at hdom8
              have hge := ordinaryDomain_ge_sourceBase (0 + 8) hdom8
              simp [sourceBase] at hge
            -- Globals and metadata of `post` equal `s`
            have hpost_ginv : GuestInv post := ⟨hginv.code, hginv.memaddrs, hginv.shMemaddrs, hginv.baseAddr⟩
            have hpost_arena : ArenaOK post := harena
            refine ⟨⟨hpost_ginv, hpost_arena⟩, Nat.le_refl _, Nat.le_refl _, ?_⟩
            intro Nd hNd hroots _hreq
            have hnd_in : nd.toNat ∈ Nd := by
              have hr := hroots "nd" (by simp)
              rw [hloc] at hr
              rcases hr with hz | hm
              · exact absurd hz hnd_ne0
              · exact hm
            obtain ⟨hNd_props, hNd_disj⟩ := hNd
            have hnd_prop := hNd_props nd.toNat hnd_in
            have hnd_ins : Inside (nodeIvl s nd.toNat) sourceBase heapLimit := hnd_prop.2.2.1
            have hns_nd := nodeSize_bounds (memW s nd.toNat)
            have hhl_lt : heapLimit < 2 ^ 64 := by decide
            have hnd_add_eq (k : Nat) (hk : k ≤ 24) :
                nd + BitVec.ofNat 64 k = BitVec.ofNat 64 (nd.toNat + k) := by
              apply BitVec.eq_of_toNat_eq
              have hlt : nd.toNat + k < 2 ^ 64 := by
                have := hnd_ins.2
                dsimp only [nodeIvl] at this
                omega
              simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
              omega
            -- Memory equality at any address not equal to `nd+8`, `nd+16`, `nd+24`
            have hmem_unchanged (a : BitVec 64)
                (ha8 : a ≠ nd + 8#64) (ha16 : a ≠ nd + 16#64) (ha24 : a ≠ nd + 24#64) :
                post.memory a = s.memory a := by
              change (if a = nd + 24#64 then HolWordLab.word 0
                else if a = nd + 16#64 then HolWordLab.word 0
                else if a = nd + 8#64 then HolWordLab.word 0
                else s.memory a) = s.memory a
              simp [ha8, ha16, ha24]
            have hwritten_bounds (a : BitVec 64)
                (hw : a = nd + 8#64 ∨ a = nd + 16#64 ∨ a = nd + 24#64) :
                a.toNat = nd.toNat + 8 ∨ a.toNat = nd.toNat + 16 ∨ a.toNat = nd.toNat + 24 := by
              have hlt24 : nd.toNat + 24 < 2 ^ 64 := by
                have := hnd_ins.2; dsimp only [nodeIvl] at this; omega
              rcases hw with rfl | rfl | rfl
              · left
                simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
                omega
              · right; left
                simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
                omega
              · right; right
                simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
                omega
            -- Helper: any address `addr < 2^64` that is not `nd.toNat + 8/16/24` has unchanged `memW`
            have hmemW_eq (addr : Nat) (haddr_lt : addr < 2 ^ 64)
                (hne8 : addr ≠ nd.toNat + 8) (hne16 : addr ≠ nd.toNat + 16) (hne24 : addr ≠ nd.toNat + 24) :
                memW post addr = memW s addr := by
              unfold memW
              rw [hmem_unchanged (BitVec.ofNat 64 addr)]
              · intro heq
                rcases hwritten_bounds _ (Or.inl heq) with h | h | h <;>
                  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt haddr_lt] at h <;> omega
              · intro heq
                rcases hwritten_bounds _ (Or.inr (Or.inl heq)) with h | h | h <;>
                  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt haddr_lt] at h <;> omega
              · intro heq
                rcases hwritten_bounds _ (Or.inr (Or.inr heq)) with h | h | h <;>
                  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt haddr_lt] at h <;> omega
            -- Every node `n ∈ Nd` keeps its kind `memW post n = memW s n` and `nodeIvl post n = nodeIvl s n`
            have hkind_eq : ∀ n ∈ Nd, memW post n = memW s n := by
              intro n hn
              have hn_ins := (hNd_props n hn).2.2.1
              have hns := nodeSize_bounds (memW s n)
              dsimp only [nodeIvl, Inside] at hn_ins
              by_cases hne : n = nd.toNat
              · subst hne
                exact hmemW_eq _ (by omega) (by omega) (by omega) (by omega)
              · have hd := hNd_disj n hn nd.toNat hnd_in hne
                dsimp only [nodeIvl, Disj] at hd
                exact hmemW_eq n (by omega) (by omega) (by omega) (by omega)
            have hivl_eq : ∀ n ∈ Nd, nodeIvl post n = nodeIvl s n := by
              intro n hn
              simp only [nodeIvl, hkind_eq n hn]
            -- KeyIn preservation helper
            have hKeyIn_keep : ∀ p len, KeyIn s Nd p len → KeyIn post Nd p len := by
              intro p len hkey
              rcases hkey with rfl | ⟨hnib, halloc, hins, hdisj⟩
              · exact Or.inl rfl
              · right
                refine ⟨?_, halloc, hins, ?_⟩
                · intro k hk
                  have hk_lt : p + k < 2 ^ 64 := by
                    dsimp only [Inside] at hins; omega
                  have hal := byteAlign_bounds (p + k) hk_lt
                  have hd_nd := hdisj nd.toNat hnd_in
                  dsimp only [Disj, nodeIvl] at hd_nd
                  have hcell_ne : ∀ off ∈ ([8, 16, 24] : List Nat),
                      (panByteAlignHOL (BitVec.ofNat 64 (p + k))).toNat ≠ nd.toNat + off := by
                    intro off hoff
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
                    rcases hoff with rfl | rfl | rfl <;> omega
                  have hmem_cell : post.memory (panByteAlignHOL (BitVec.ofNat 64 (p + k))) =
                      s.memory (panByteAlignHOL (BitVec.ofNat 64 (p + k))) := by
                    apply hmem_unchanged
                    · intro heq
                      rcases hwritten_bounds _ (Or.inl heq) with h | h | h
                      · exact hcell_ne 8 (by simp) h
                      · exact hcell_ne 16 (by simp) h
                      · exact hcell_ne 24 (by simp) h
                    · intro heq
                      rcases hwritten_bounds _ (Or.inr (Or.inl heq)) with h | h | h
                      · exact hcell_ne 8 (by simp) h
                      · exact hcell_ne 16 (by simp) h
                      · exact hcell_ne 24 (by simp) h
                    · intro heq
                      rcases hwritten_bounds _ (Or.inr (Or.inr heq)) with h | h | h
                      · exact hcell_ne 8 (by simp) h
                      · exact hcell_ne 16 (by simp) h
                      · exact hcell_ne 24 (by simp) h
                  have hmemb_eq : memB post (p + k) = memB s (p + k) := by
                    unfold memB
                    rw [hmem_cell]
                    rfl
                  rw [hmemb_eq]
                  exact hnib k hk
                · intro n hn
                  rw [hivl_eq n hn]
                  exact hdisj n hn
            -- Witness `Nd' := Nd`
            refine ⟨Nd, ?_, fun _ hn => hn, hkind_eq, fun _ hn => Or.inl hn, ?_, ?_, ?_⟩
            · -- `NodeHeap post Nd`
              refine ⟨?_, ?_⟩
              · intro n hn
                have hp_n := hNd_props n hn
                have hn_ins := hp_n.2.2.1
                have hns := nodeSize_bounds (memW s n)
                dsimp only [nodeIvl, Inside] at hn_ins
                -- Any offset `off ≥ 32` inside `nodeIvl s n` is unchanged in `post`
                have hoff_eq (off : Nat) (hoff32 : 32 ≤ off) (hoff_hi : off < nodeSize (memW s n)) :
                    memW post (n + off) = memW s (n + off) := by
                  by_cases hne : n = nd.toNat
                  · subst hne
                    exact hmemW_eq _ (by omega) (by omega) (by omega) (by omega)
                  · have hd := hNd_disj n hn nd.toNat hnd_in hne
                    dsimp only [nodeIvl, Disj] at hd
                    exact hmemW_eq _ (by omega) (by omega) (by omega) (by omega)
                rw [hkind_eq n hn, hivl_eq n hn]
                refine ⟨hp_n.1, hp_n.2.1, hp_n.2.2.1, ?_, ?_, ?_, ?_⟩
                · -- `WordsOK post (nodeIvl s n)`
                  rcases hp_n.2.2.2.1 with ⟨ha1, ha2, hwok⟩
                  refine ⟨ha1, ha2, fun k hk => ?_⟩
                  obtain ⟨cw0, hdom_k, _⟩ := hwok k hk
                  have hdom_post : post.memaddrs (BitVec.ofNat 64 ((nodeIvl s n).1 + 8 * k)) := hdom_k
                  cases hcell : post.memory (BitVec.ofNat 64 ((nodeIvl s n).1 + 8 * k)) with
                  | word cw => exact ⟨cw, hdom_post, hcell⟩
                · -- `memW s n = 2 → RootIn Nd (memW post (n + 48))`
                  intro hk2
                  have hsz2 : nodeSize (memW s n) = 56 := by simp [nodeSize, hk2]
                  rw [hoff_eq 48 (by omega) (by omega)]
                  exact hp_n.2.2.2.2.1 hk2
                · -- `memW s n = 3 → ∀ i < 16, RootIn Nd (memW post (n + 32 + 8 * i))`
                  intro hk3 i hi
                  have hsz3 : nodeSize (memW s n) = 176 := by simp [nodeSize, hk3]
                  have heq_i : n + 32 + 8 * i = n + (32 + 8 * i) := by omega
                  rw [heq_i, hoff_eq (32 + 8 * i) (by omega) (by omega), ← heq_i]
                  exact hp_n.2.2.2.2.2.1 hk3 i hi
                · -- `(memW s n = 1 ∨ memW s n = 2) → KeyIn post Nd (memW post (n + 32)) (memW post (n + 40))`
                  refine ⟨?_, ?_, ?_, ?_⟩
                  · intro hk12
                    have hsz12 : 56 ≤ nodeSize (memW s n) := by
                      rcases hk12 with hk1 | hk2
                      · simp [nodeSize, hk1]
                      · simp [nodeSize, hk2]
                    rw [hoff_eq 32 (by omega) (by omega), hoff_eq 40 (by omega) (by omega)]
                    exact hKeyIn_keep _ _ (hp_n.2.2.2.2.2.2.1 hk12)
                  · by_cases hne : n = nd.toNat
                    · subst hne
                      have h16_eq : post.memory (BitVec.ofNat 64 (nd.toNat + 16)) = .word 0 := by
                        rw [← hnd_add_eq 16 (by omega)]
                        change (if nd + 16#64 = nd + 24#64 then HolWordLab.word 0
                          else if nd + 16#64 = nd + 16#64 then HolWordLab.word 0
                          else if nd + 16#64 = nd + 8#64 then HolWordLab.word 0
                          else s.memory (nd + 16#64)) = .word 0
                        have hne24 : nd + 16#64 ≠ nd + 24#64 := by
                          intro he
                          have h1 := congrArg BitVec.toNat he
                          rw [hnd_add_eq 16 (by omega), hnd_add_eq 24 (by omega),
                            BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                            Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h1
                          omega
                        simp [hne24]
                      unfold memW
                      rw [h16_eq]
                      decide
                    · have hd := hNd_disj n hn nd.toNat hnd_in hne
                      dsimp only [nodeIvl, Disj] at hd
                      rw [hmemW_eq (n + 16) (by omega) (by omega) (by omega) (by omega)]
                      exact hp_n.2.2.2.2.2.2.2.1
                  · intro hk1
                    have hsz1 : nodeSize (memW s n) = 64 := by simp [nodeSize, hk1]
                    rw [hoff_eq 56 (by omega) (by omega)]
                    exact hp_n.2.2.2.2.2.2.2.2.1 hk1
                  · intro hk3
                    have hsz3 : nodeSize (memW s n) = 176 := by simp [nodeSize, hk3]
                    rw [hoff_eq 168 (by omega) (by omega)]
                    exact hp_n.2.2.2.2.2.2.2.2.2 hk3
              · intro n hn m hm hne
                rw [hivl_eq n hn, hivl_eq m hm]
                exact hNd_disj n hn m hm hne
            · -- `FrameOutside`
              intro a hkeep _hfresh
              have hnotin : ¬ (a = nd + 8#64 ∨ a = nd + 16#64 ∨ a = nd + 24#64) := by
                intro hw
                have hhit : CellHits a.toNat (nodeIvl s nd.toNat) := by
                  dsimp only [CellHits, nodeIvl]
                  rcases hwritten_bounds a hw with h | h | h <;> omega
                exact hkeep (nodeIvl s nd.toNat)
                  (List.mem_append_left _ (List.mem_map.mpr ⟨nd.toNat, hnd_in, rfl⟩)) hhit
              exact hmem_unchanged a
                (fun h => hnotin (Or.inl h))
                (fun h => hnotin (Or.inr (Or.inl h)))
                (fun h => hnotin (Or.inr (Or.inr h)))
            · -- Globals unchanged
              intro _ _; rfl
            · -- Return value is `0` (`RootIn Nd 0`)
              intro v hv
              injection hv with hv1
              injection hv1 with hv2
              subst hv2
              exact ⟨0, rfl, Or.inl rfl⟩
    · rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_store] at hres
      simp [evalHOLExact, evalListHOLExact, hnd, valueIsWord] at hres
      exact absurd hres not_resumes_error
    · have hnd' : s.locals.lookup (ofString "nd") = some (.nStruct nm fs) := hnd
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_store] at hres
      simp [evalHOLExact, evalListHOLExact, hnd', valueIsWord] at hres
      exact absurd hres not_resumes_error

end InitECandidate.Solver.Wave8Contracts.M25
