import InitECandidate.Solver.PanRunBounded
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat

set_option Elab.async false

/-! Source: LightSpec.lean; Opus port from 3ea193df0. -/

/-! PROPOSED STATEMENTS ONLY (Wave 8, mission 9409f9a9, track `guestinv-opus55`), revision 8
(round-5 fixes: role-typed tables with pinned key lengths, exit-world avoidance of constructor
results, guarded-loop progress contracts; the per-revision change lists are in
`campaign/notes/guestinv/DESIGN.md` §0, revision 8 in §0.0 and §0.2c; no `fb_*` changed).

Replaces the presumed-false all-state `TerminatingFunBounded "main"` route by a guarded one.
Revision 2 answered the round-1 quorum (`campaign/reviews/guestinv-r1.md`):

* `GuestInv` (§2) is *metadata only* (code, memory domains, base address). Every Pancake
  evaluation preserves it (`guestInv_evaluate`, proved), so every call / decCall / handler / seq
  composition needs no preservation side condition.
* Every function on `main`'s call graph gets its own bound `K.«f»` (§6, generated mechanically
  from `Guest/SoftwareAst.lean` by `campaign/notes/guestinv/scripts/coverage.py`), equal to the
  sum over the body of `K(callee) + 1` per call and `(N + 1) * (body + 1)` per loop, where `N` is
  the loop's iteration bound, from a measure that holds for ARBITRARY memory and globals wherever
  one exists.
* Five loops have no arbitrary-memory measure: `run_frames` (EVM gas), `htab_truncate`
  (count in memory), `_decode_witness_node_body` (needs heap/scratch separation) and the two MPT
  update loops. They and their callers form the *guarded tier* (§7), whose leaves carry explicit
  memory contracts (`HtabWF`, `EvmInv` with a gas-value-free potential, `WorldOK`).

Revision 3 answers the round-2 quorum (`campaign/reviews/guestinv-r2.md`):

* `htab_new_spec` / `htab_new_scratch_spec` are guarded by `key_len ∈ htabKeyLens`
  (`HtabNewReady`, item 1).
* `EvmInv` requires stack room in every suspended frame (`FrameRoom`), so `finish_child`'s
  `stack_push` on the parent never allocates below the child's mark (item 2).
* The combinator set is closed and every combinator is PROVED (item 3): tail call
  (`tailCall_on`), handler call (`callHandle_guestInv`), the stationary `while` rule
  (`while_rank_stationary`, with `while_rank` as a corollary), `dec` for guards that read locals
  (`dec_onLocals` with `LocalsOnly`, instantiated for every guard), and the guarded `decCall_on`
  and condition-aware `ite_cond_on` that the guarded leaves need. `htab_del_progress_spec` gives
  `htab_truncate` its count decrement.
* The bridge (§4) is unchanged and proved; `K_pan_budget` (§8) is proved by `decide`; no `K.«f»`
  changed.

Rationale, the per-loop justification table, the list of `sorry`s and the list of statements
changed since revision 2 are in `campaign/notes/guestinv/DESIGN.md`. `sorry` appears only in leaf
theorem bodies, never in a definition or a combinator.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8HtabAstra

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanRunBounded

/-! ## 1. Layout constants (all from `InitE.Parameters` / `Guest/SoftwareAst.lean`) -/

/-- Upper end of the bump heap: `alloc` traps unless the new `heap_ptr ≤ 0xb0000000`. -/
def heapLimit : Nat := scratchStart

/-- `journal_cap` is only ever assigned `0` (declaration) or `524288` (`state_init`,
`Guest/SoftwareAst.lean:12768`). -/
def journalCapMax : Nat := 524288

/-- Bytes of `ordinaryDomain = [sourceBase, heapEnd)` (aligned cells only). A loop that loads or
stores a strictly increasing address on every iteration errors within this many iterations. -/
def domainBytes : Nat := heapEnd - sourceBase

theorem domainBytes_eq : domainBytes = 31104957928 := by decide

/-- Maximum key length of every guest hash table. `htab_new`/`htab_new_scratch` are called with
the literal key lengths 20, 28, 32, 52 and 60 only (`bal_init` uses 28 and 60,
`Guest/SoftwareAst.lean:13873-13875`); round 1 wrongly had 52. -/
def maxKeyLen : Nat := 60

/-- Frame-chain length bound used by the EVM potential. Each active frame owns at least
280 (record) + 1024 (stack) + 104 (continuation) disjoint scratch bytes and the scratch arena has
`0xb0bee000 - 0xb0000000 = 12509184` bytes, so `EvmInv` forces at most 8884 frames. -/
def maxChain : Nat := 16384

/-! ## 2. `GuestInv`: metadata only, preserved by every evaluation

Round 1 put four global-variable facts into `GuestInv` (`heap_ptr ≤ 0xb0000000`,
`ArenaOK frame_mem_ptr scratch_ptr`, `journal_n ≤ journal_cap ≤ 2^19`, all globals are words).
Each of them is broken by some call whose destination or argument comes from memory or from an
unrelated callee: `call heap_mark → journal_n` (round 1, item 1), `scratch_release(load(rec+48))`
and `frame_mem_release(load(rec+56))` in `finish_child`. In revision 2 every unguarded bound holds
for arbitrary memory AND arbitrary globals, so `GuestInv` keeps only the four fields that no
Pancake program can change. Preservation is a theorem about the semantics (`guestInv_evaluate`). -/

/-- The guest invariant: code and the three memory-domain/base fields of the covered entry. -/
structure GuestInvData {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop where
  code : s.code = originalRuntimeCode
  memaddrs : s.memaddrs = ordinaryDomain
  shMemaddrs : s.shMemaddrs = sharedDomain
  baseAddr : s.baseAddr = BitVec.ofNat 64 sourceBase

def GuestInv : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => GuestInvData s

/-- `name` is a global bound to the word `w`. -/
def GlobalWord {F : Type} (s : PanSemStateFiniteExact 64 F) (name : String) (w : BitVec 64) :
    Prop :=
  s.globals.lookup (ofString name) = some (.val (.word w))

/-! ### Preservation (proved) -/

/-- `baseAddr` is never changed by evaluation (Flapjack `evaluateInvariantsHOLFinite`). -/
theorem evaluate_baseAddr {F : Type} (state : PanSemStateFiniteExact 64 F)
    (program : ProgHOL 64) :
    (evaluateHOLFiniteState state program).2.baseAddr = state.baseAddr := by
  have invariant := evaluateInvariantsHOLFinite program
    (PanPropsEvalStateFiniteExact.ofPanSemFinite state)
    (evaluateHOLFiniteState state program).1
    (PanPropsEvalStateFiniteExact.ofPanSemFinite (evaluateHOLFiniteState state program).2) (by
      simp only [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,
        PanPropsEvalStateFiniteExact.toPanSemFinite_ofPanSemFinite])
  exact invariant.2.2.2.2.1

/-- Every evaluation of every program preserves `GuestInv` (whatever its result). -/
theorem guestInv_evaluate {F : Type} (s : PanSemStateFiniteExact 64 F) (prog : ProgHOL 64)
    (h : GuestInv s) : GuestInv (evaluateHOLFiniteState s prog).2 := by
  obtain ⟨c, m, sh, b⟩ := h
  have hm := PanRunBounded.evaluateHOLFiniteState_metadata s prog
  exact ⟨hm.1.trans c, hm.2.1.trans m, hm.2.2.2.1.trans sh, (evaluate_baseAddr s prog).trans b⟩

theorem guestInv_congr {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (hcode : t.code = s.code) (hmem : t.memaddrs = s.memaddrs) (hsh : t.shMemaddrs = s.shMemaddrs)
    (hbase : t.baseAddr = s.baseAddr) (h : GuestInv s) : GuestInv t := by
  obtain ⟨c, m, sh, b⟩ := h
  exact ⟨hcode.trans c, hmem.trans m, hsh.trans sh, hbase.trans b⟩

theorem guestInv_callEntry {F : Type} (s : PanSemStateFiniteExact 64 F)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (h : GuestInv s) :
    GuestInv (callEntryStateHOLFinite s callee) :=
  guestInv_congr (s := s) rfl rfl rfl rfl h

theorem guestInv_with_locals_clock {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (h : GuestInv s) :
    GuestInv { s with locals := locals, clock := k } :=
  guestInv_congr (s := s) rfl rfl rfl rfl h

theorem guestInv_setVar {F : Type} (name : MlS) (v : ValueHOL 64)
    (s : PanSemStateFiniteExact 64 F) (h : GuestInv s) : GuestInv (setVarHOLFinite name v s) :=
  guestInv_congr (s := s) rfl rfl rfl rfl h

/-! ## 5. Memory views and memory contracts (guarded tier only)

Everything in this section is used only by the guarded tier (§7). The unguarded tier (§6) never
looks at memory contents. -/

/-- The word stored at the (aligned) address `a` (`HolWordLab` has the single constructor
`.word`). -/
def memW {F : Type} (s : PanSemStateFiniteExact 64 F) (a : Nat) : Nat :=
  match s.memory (BitVec.ofNat 64 a) with
  | .word w => w.toNat

/-- `a` is an in-domain cell holding a word (what a successful `load` needs). -/
def WordAt {F : Type} (s : PanSemStateFiniteExact 64 F) (a : Nat) : Prop :=
  ∃ w : BitVec 64, s.memaddrs (BitVec.ofNat 64 a) ∧ s.memory (BitVec.ofNat 64 a) = .word w

/-- The global `name` as a natural number (`0` if it is not a word). -/
def globN {F : Type} (s : PanSemStateFiniteExact 64 F) (name : String) : Nat :=
  match s.globals.lookup (ofString name) with
  | some (.val (.word w)) => w.toNat
  | _ => 0

/-- The local `name` as a natural number (`0` if absent or not a word). -/
def locN {F : Type} (s : PanSemStateFiniteExact 64 F) (name : String) : Nat :=
  match s.locals.lookup (ofString name) with
  | some (.val (.word w)) => w.toNat
  | _ => 0

/-- A memory interval `(base, length)` in bytes. -/
abbrev Ivl := Nat × Nat

def Inside (i : Ivl) (lo hi : Nat) : Prop := lo ≤ i.1 ∧ i.1 + i.2 ≤ hi

def Disj (i j : Ivl) : Prop := i.1 + i.2 ≤ j.1 ∨ j.1 + j.2 ≤ i.1

def InIvl (a : Nat) (i : Ivl) : Prop := i.1 ≤ a ∧ a < i.1 + i.2

/-- Every aligned cell of `i` is an in-domain word. -/
def WordsOK {F : Type} (s : PanSemStateFiniteExact 64 F) (i : Ivl) : Prop :=
  i.1 % 8 = 0 ∧ i.2 % 8 = 0 ∧ ∀ k, k < i.2 / 8 → WordAt s (i.1 + 8 * k)

/-! ### Allocator globals -/

/-- The four allocator globals describe separated arenas: the bump heap
`[sourceBase, heap_ptr) ⊆ [sourceBase, 0xb0000000)`, frame memory growing up from `0xb0000000` to
`frame_mem_ptr`, scratch growing down from `0xb0bee000` to `scratch_ptr`. Holds after `mem_init`
(`mem_init_arenaReady`); `alloc`/`scratch_alloc`/`frame_mem_alloc` preserve it by their own
checks; `heap_release`/`scratch_release`/`frame_mem_release` preserve it when their argument is a
mark taken by the same activation (the contract of every caller, §7).

Revision 6 (round-4 Astra item 7): the three pointers are 8-byte aligned. `mem_init` sets them to
`sourceBase`, `0xb0bee000`, `0xb0000000` (all aligned). `alloc` and `frame_mem_alloc` return the
OLD pointer `p` and set the new one to `(p + n + 7) & -8`; `scratch_alloc` sets and returns
`(p - n) & -8` (AST 66, 110, 154). So with aligned pointers every allocation returns an aligned
block and leaves the pointers aligned. The release marks are earlier pointer values (`heap_mark`,
`scratch_mark`, and the continuation marks, aligned by `MarksOK`). Without alignment,
`frame_mem_ptr = 0xb0000001` made `frame_open`'s `frame_mem_alloc(1024)` return an unaligned EVM
memory, which `WordsOK` (in `FrameWF`) rejects. Every contract that ends in `ArenaReady` (all of
§7) now also re-establishes alignment. -/
def ArenaOK {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  sourceBase ≤ globN s "heap_ptr" ∧ globN s "heap_ptr" ≤ heapLimit ∧
  scratchStart ≤ globN s "frame_mem_ptr" ∧ globN s "frame_mem_ptr" ≤ globN s "scratch_ptr" ∧
  globN s "scratch_ptr" ≤ scratchEnd ∧
  globN s "heap_ptr" % 8 = 0 ∧ globN s "frame_mem_ptr" % 8 = 0 ∧ globN s "scratch_ptr" % 8 = 0

def ArenaReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => GuestInv s ∧ ArenaOK s

/-- `i` lies in currently allocated heap or scratch memory. -/
def Allocated {F : Type} (s : PanSemStateFiniteExact 64 F) (i : Ivl) : Prop :=
  Inside i sourceBase (globN s "heap_ptr") ∨ Inside i (globN s "scratch_ptr") scratchEnd

/-! ### Crit-bit tables (round-1 item 4)

Layout (`htab_new`, `Guest/SoftwareAst.lean:4867`): header words at `t + 8k`,
`k = 0..10` = key_len, stride, cap, count, keys, nodes, order, root, next, free, ncap.
Node `n` occupies `nodes + 32n .. +32`: `+0` parent (or next free node), `+8`/`+16` children of
an internal node, resp. value / order position of a leaf, `+24` crit bit (`8·key_len` marks a
leaf). Node `0` is the null node. -/

def hdr {F : Type} (s : PanSemStateFiniteExact 64 F) (t k : Nat) : Nat := memW s (t + 8 * k)

def nodeF {F : Type} (s : PanSemStateFiniteExact 64 F) (nodes n off : Nat) : Nat :=
  memW s (nodes + 32 * n + off)

/-- The four memory blocks of table `t`: header, keys, nodes, order. -/
def htabFootprint {F : Type} (s : PanSemStateFiniteExact 64 F) (t : Nat) : List Ivl :=
  [(t, 88), (hdr s t 4, (hdr s t 10 + 1) * hdr s t 1), (hdr s t 5, (hdr s t 10 + 1) * 32),
   (hdr s t 6, (hdr s t 10 + 1) * 8)]

/-- The free list starting at `head`, linked through node field `+0`, is exactly `Fr`. -/
def FreeChain {F : Type} (s : PanSemStateFiniteExact 64 F) (nodes : Nat) : Nat → List Nat → Prop
  | head, [] => head = 0
  | head, f :: rest => head = f ∧ FreeChain s nodes (nodeF s nodes f 0) rest

/-- Structural crit-bit invariant (replaces round 1's `HtabWF`):
* the four blocks are in-domain words, pairwise disjoint;
* `1 ≤ key_len ≤ 60`, `stride = round8 key_len`, `2 ≤ ncap`, `1 ≤ next ≤ ncap + 1`;
* the allocated node indices `[1, next)` split into live leaves `L` (listed by `order[0..count)`,
  so `count = |L|`), internal nodes `I` with `|I| + 1 = count` (or both empty) and the free list
  `Fr` (headed at `t+72`); hence `2·count - 1 ≤ ncap`, so `count ≤ ncap` and every index the code
  computes stays inside its block;
* a leaf has crit bit `8·key_len` and order position `+16` equal to its index in `L`; its value
  `+8` is UNCONSTRAINED (round 1 wrongly bounded it, and `htab_set` overwrites it);
* an internal node has crit bit `< 8·key_len`, two distinct children in `L ∪ I` whose parent
  field `+0` points back to it; the root `t+56` is `0` iff the table is empty, has parent `0`, and
  is nobody's child; every other live node's parent is an internal node that has it as a child;
* rooted and acyclic (round-2 Astra item 4): some depth `dep` strictly decreases from every
  non-root live node to its parent, so following parents from any live node reaches the root,
  and descending through children from the root reaches a leaf. Without it a disconnected cycle
  (`1=(0,7,0,8)`, `2=(3,9,1,8)`, `3=(3,2,3,0)`, root `1`, count `2`) satisfied `HtabWF`, and
  `htab_del` of leaf 1 broke it.
The fields `cap` (`+16`) and the values are free. -/
def HtabWF {F : Type} (s : PanSemStateFiniteExact 64 F) (t : Nat) : Prop :=
  let klen := hdr s t 0
  let cnt := hdr s t 3
  let nodes := hdr s t 5
  let order := hdr s t 6
  let root := hdr s t 7
  let next := hdr s t 8
  let ncap := hdr s t 10
  let nd := nodeF s nodes
  (∀ i ∈ htabFootprint s t, Inside i sourceBase heapEnd ∧ WordsOK s i) ∧
  (htabFootprint s t).Pairwise Disj ∧
  1 ≤ klen ∧ klen ≤ maxKeyLen ∧ hdr s t 1 = (klen + 7) / 8 * 8 ∧
  2 ≤ ncap ∧ 1 ≤ next ∧ next ≤ ncap + 1 ∧
  ∃ L I Fr : List Nat,
    L.length = cnt ∧ (L ++ I ++ Fr).Nodup ∧
    (∀ n, n ∈ L ++ I ++ Fr ↔ 1 ≤ n ∧ n < next) ∧
    ((cnt = 0 ∧ I = []) ∨ I.length + 1 = cnt) ∧
    (∀ (i : Nat) (h : i < L.length),
      memW s (order + 8 * i) = L[i] ∧ nd L[i] 24 = 8 * klen ∧ nd L[i] 16 = i) ∧
    (∀ n ∈ I, nd n 24 < 8 * klen ∧ nd n 8 ∈ L ++ I ∧ nd n 16 ∈ L ++ I ∧ nd n 8 ≠ nd n 16 ∧
      nd (nd n 8) 0 = n ∧ nd (nd n 16) 0 = n) ∧
    (cnt = 0 → root = 0) ∧ (0 < cnt → root ∈ L ++ I ∧ nd root 0 = 0) ∧
    (∀ n ∈ I, nd n 8 ≠ root ∧ nd n 16 ≠ root) ∧
    (∀ n ∈ L ++ I, n ≠ root → nd n 0 ∈ I) ∧
    (∃ dep : Nat → Nat, ∀ n ∈ L ++ I, n ≠ root →
      (nd (nd n 0) 8 = n ∨ nd (nd n 0) 16 = n) ∧ dep (nd n 0) < dep n) ∧
    FreeChain s nodes (hdr s t 9) Fr

/-- Regression (round-2 Astra item 4): no live non-root node is its own parent. Astra's
counterexample has node `3` with parent `3`, so it no longer satisfies `HtabWF`. -/
theorem htabWF_no_self_parent {F : Type} (s : PanSemStateFiniteExact 64 F) (t : Nat)
    (h : HtabWF s t) : ∃ L I : List Nat, (L.length = hdr s t 3) ∧
      ∀ n ∈ L ++ I, n ≠ hdr s t 7 → nodeF s (hdr s t 5) n 0 ≠ n := by
  obtain ⟨-, -, -, -, -, -, -, -, L, I, -, hlen, -, -, -, -, -, -, -, -, -, ⟨dep, hdep⟩, -⟩ := h
  refine ⟨L, I, hlen, fun n hn hroot heq => ?_⟩
  have := (hdep n hn hroot).2
  rw [heq] at this
  exact Nat.lt_irrefl _ this

/-- Live values of table `t` (the `+8` field of every live leaf). -/
def HtabValuesIn {F : Type} (s : PanSemStateFiniteExact 64 F) (t : Nat) (S : List Nat) : Prop :=
  ∀ i, i < hdr s t 3 → nodeF s (hdr s t 5) (memW s (hdr s t 6 + 8 * i)) 8 ∈ S

/-- The 8-byte memory cell at address `a` meets the byte interval `i` (revision 6, round-4 Astra
item 4). Memory is a map from cell addresses to words; a byte store changes the whole aligned cell
holding the byte. For an aligned `a` and a word-aligned `i` (base and length multiples of 8) this is
exactly `InIvl a i`. -/
def CellHits (a : Nat) (i : Ivl) : Prop := i.1 < a + 8 ∧ a < i.1 + i.2

/-- Memory outside `keep ∪ fresh` is unchanged from `s` to `post`. Addresses are the 64-bit
words themselves, tested through `toNat` (round-2 Astra item 1: quantifying over `a : Nat` and
reading `BitVec.ofNat 64 a` made `x + 2^64` an outside alias of every changed `x`).

Revision 6 (round-4 Astra item 4): the frame is at cell granularity. A cell may change iff it
MEETS a kept region or the fresh region (`CellHits`), not only if its address lies inside one. So a
byte region `(a + 1, 1)` declares the whole cell `a`. Before, `memzero(a + 1, 1)` changed the word
at `a`, outside `[a + 1, a + 2)`, and every byte-writing contract (`ww_memcpy`, `ww_memzero`,
`ww_rlp_encode_bytes`, `ww_rlp_encode_word`, `ww_compute_contract_address`,
`ww_recover_sender_with_chain_id`, the `KeepsOn`/`NodeFn` contracts of byte writers, …) was false
for unaligned regions. The change is in this one definition, so every frame (`WritesWithin`,
`HtabExit`, `UnionExit`, `HtabNewExit`, `MptExit`, `NodeFnExit`) uses it. An owned object is
word-aligned (`WordsOK`); if it is byte-disjoint from every kept region, none of its cells is hit,
so the frame still protects it exactly as before. -/
def FrameOutside {F : Type} (s post : PanSemStateFiniteExact 64 F) (keep : List Ivl)
    (fresh : Ivl) : Prop :=
  ∀ a : BitVec 64, (∀ i ∈ keep, ¬ CellHits a.toNat i) → ¬ CellHits a.toNat fresh →
    post.memory a = s.memory a

/-- Regression (round-2 Astra item 1): a single store inside `fresh` respects the frame. -/
example {F : Type} (s : PanSemStateFiniteExact 64 F) (x : BitVec 64) (w : HolWordLab 64) :
    FrameOutside s { s with memory := fun b => if b = x then w else s.memory b } [] (x.toNat, 8) := by
  intro a _ hout
  have hne : a ≠ x := by
    rintro rfl
    exact hout ⟨by omega, by omega⟩
  simp [hne]

/-- Regression (revision 6, round-4 Astra item 4): writing the cell `x` for a byte store at
`x + 1` respects the frame of the one-byte region `(x + 1, 1)`. -/
example {F : Type} (s : PanSemStateFiniteExact 64 F) (x : BitVec 64) (w : HolWordLab 64) :
    FrameOutside s { s with memory := fun b => if b = x then w else s.memory b }
      [(x.toNat + 1, 1)] (0, 0) := by
  intro a hkeep _
  have hne : a ≠ x := by
    rintro rfl
    exact hkeep _ (List.mem_singleton.2 rfl) ⟨by omega, by omega⟩
  simp [hne]

/-- Regression (revision 6): an aligned cell outside an aligned region is not hit, so for
word-aligned objects the cell frame is the old address frame. -/
theorem cellHits_aligned {a : Nat} {i : Ivl} (ha : a % 8 = 0) (hi1 : i.1 % 8 = 0)
    (h : CellHits a i) : InIvl a i := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨by omega, h2⟩

/-- Normal return of a function body from an entry state (callee-entry formulation). -/
def FunEnsures (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Prop)
    (fname : MlS) : Prop :=
  ∃ (params : List (MlS × ShapeHOL)) (body : ProgHOL 64) (retShape : ShapeHOL),
    originalRuntimeCode.lookup fname = some (params, body, retShape) ∧
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → P s →
      ∀ v, (evaluateHOLFiniteState s body).1 = some (.returned v) →
        Q s (evaluateHOLFiniteState s body).2

/-- Entry of an `htab_*` function: the table parameter `t` is well formed and allocated, the
arenas are separated. -/
def HtabArgWF : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ HtabWF s (locN s "t") ∧
    ∀ i ∈ htabFootprint s (locN s "t"), Allocated s i

/-- Exit contract of the table-mutating functions (`htab_set`, `htab_del`, `htab_truncate`):
the table stays well formed, the heap only grows, the new footprint is the old one plus freshly
allocated heap, and nothing else in memory changes (the write frame that keeps every OTHER table,
frame record and buffer intact). Globals other than `heap_ptr` are unchanged. -/
def HtabExit : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Prop :=
  fun s post =>
    let t := locN s "t"
    let fresh : Ivl := (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr")
    ArenaReady post ∧ HtabWF post t ∧
    globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
    (∀ i ∈ htabFootprint post t, Allocated post i ∧
      ((∃ j ∈ htabFootprint s t, Inside i j.1 (j.1 + j.2)) ∨ Inside i fresh.1 (fresh.1 + fresh.2))) ∧
    FrameOutside s post (htabFootprint s t) fresh ∧
    (∀ name, name ≠ "heap_ptr" → s.globals.lookup (ofString name) = post.globals.lookup (ofString name))

/-- Outcome specification of a function body from its callee-entry state. -/
def FunSpec (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop)
    (fname : MlS) : Prop :=
  ∃ (params : List (MlS × ShapeHOL)) (body : ProgHOL 64) (retShape : ShapeHOL),
    originalRuntimeCode.lookup fname = some (params, body, retShape) ∧
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → P s →
      (evaluateHOLFiniteState s body).1 ≠ some .timeOut →
      Q s (evaluateHOLFiniteState s body).1 (evaluateHOLFiniteState s body).2

/-- `Q` on normal return only. -/
def OnReturn (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Prop) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop :=
  fun s r post => ∀ v, r = some (.returned v) → Q s post

def HtabDelProgress : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F →
    Prop :=
  fun s post => hdr post (locN s "t") 3 + 1 = hdr s (locN s "t") 3 ∨
    post = { s with locals := post.locals, clock := post.clock }

def LoopActive (condition : ExpHOL 64) {F : Type} (state : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ word : BitVec 64,
    evalHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      condition = some (.val (.word word)) ∧ word ≠ 0

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

def CondFalse (cond : ExpHOL 64) {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  @evalHOLExact 64 F _ s.toExact
    (fun address => Classical.propDecidable (s.memaddrs address)) cond = some (.val (.word 0))

noncomputable abbrev evalAt {F : Type} (t : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) :
    Option (ValueHOL 64) :=
  @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) e

theorem evalAt_cmp {F : Type} (t : PanSemStateFiniteExact 64 F) (op : Cmp) (l r : ExpHOL 64)
    (w : BitVec 64) (h : evalAt t (.cmp op l r) = some (.val (.word w))) :
    ∃ a b : BitVec 64, evalAt t l = some (.val (.word a)) ∧ evalAt t r = some (.val (.word b)) ∧
      w = if Flapjack.Compiler.Encoders.Asm.wordCmpHOL op a b then 1 else 0 := by
  simp only [evalAt, evalHOLExact] at h ⊢
  split at h
  · rename_i a b ha hb
    exact ⟨a, b, ha, hb, (by simpa using h.symm)⟩
  · cases h


end InitECandidate.Solver.Wave8HtabAstra

/-! Source: Base.lean; Opus port from 3ea193df0. -/

/-! Shared infrastructure for the hash-table leaves (`wave8/leaves-htab-opus55`).

* `onOf`: an unconditional bound is a bound under any guard;
* `LocFrame` / `locOnly`: a loop-free program that only writes locals changes nothing but the
  locals and the clock;
* the no-repeat `while` rule (`while_noRepeat`), ported from `wave8/step0-opus55`
  (`PanTerminatingNoRepeat`, proved there), restated over the spec's `LoopActive`,
  `evaluate_ne_of_clock_lt` and `while_unfold_continue`;
* `while_oneWord`: a read-only loop whose only changing local is one word is bounded by
  `(2^64 + 1) * (B + 1)`.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace InitECandidate.Solver.Wave8HtabAstra.Htab

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8HtabAstra

/-! ## Local frames of loop-free local-only programs -/

/-- `t` agrees with `s` on every field but the locals and the clock. -/
def LocFrame {F : Type} (s t : PanSemStateFiniteExact 64 F) : Prop :=
  t = { s with locals := t.locals, clock := t.clock }

theorem LocFrame.refl {F : Type} (s : PanSemStateFiniteExact 64 F) : LocFrame s s := by
  cases s; rfl

theorem LocFrame.trans {F : Type} {s t u : PanSemStateFiniteExact 64 F}
    (h1 : LocFrame s t) (h2 : LocFrame t u) : LocFrame s u := by
  unfold LocFrame at *
  rw [h2]; rw [h1]

/-- Loop-free programs whose only effects are on locals. -/
def locOnly : ProgHOL 64 → Bool
  | .dec _ _ _ body => locOnly body
  | .seq first second => locOnly first && locOnly second
  | .ite _ yes no => locOnly yes && locOnly no
  | .assign .local _ _ => true
  | .skip | .break | .continue | .annot _ _ | .raise _ _ | .return _ => true
  | _ => false

theorem locFrame_eval {F : Type} : ∀ (p : ProgHOL 64), locOnly p = true →
    ∀ (s : PanSemStateFiniteExact 64 F), LocFrame s (evaluateHOLFiniteState s p).2
  | .skip, _, s => by rw [evaluateHOLFiniteState_skip]; exact LocFrame.refl s
  | .break, _, s => by rw [evaluateHOLFiniteState_break]; exact LocFrame.refl s
  | .continue, _, s => by rw [evaluateHOLFiniteState_continue]; exact LocFrame.refl s
  | .annot _ _, _, s => by rw [evaluateHOLFiniteState_annot]; exact LocFrame.refl s
  | .raise _ _, _, s => by
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split
      · rfl
      · exact LocFrame.refl s
    · exact LocFrame.refl s
  | .return _, _, s => by
    rw [evaluateHOLFiniteState_return]
    split
    · exact LocFrame.refl s
    · split
      · rfl
      · exact LocFrame.refl s
  | .assign kind name e, h, s => by
    cases kind with
    | global => simp [locOnly] at h
    | «local» =>
      rw [evaluateHOLFiniteState_assign]
      split
      · exact LocFrame.refl s
      · split
        · rfl
        · exact LocFrame.refl s
  | .dec name sh init body, h, s => by
    have hb : locOnly body = true := by simpa [locOnly] using h
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · exact LocFrame.refl s
    · rename_i val _
      split
      · have ih := locFrame_eval body hb (setVarHOLFinite name val s)
        unfold LocFrame at ih ⊢
        dsimp only
        rw [ih]; rfl
      · exact LocFrame.refl s
  | .seq first second, h, s => by
    have h12 : locOnly first = true ∧ locOnly second = true := by
      simpa [locOnly, Bool.and_eq_true] using h
    rw [evaluateHOLFiniteState_seq_line780]
    have ih1 := locFrame_eval first h12.1 s
    rcases hr1 : evaluateHOLFiniteState s first with ⟨r1, mid⟩
    rw [hr1] at ih1
    dsimp only at ih1 ⊢
    cases r1 with
    | none => exact ih1.trans (locFrame_eval second h12.2 mid)
    | some _ => exact ih1
  | .ite cond yes no, h, s => by
    have h12 : locOnly yes = true ∧ locOnly no = true := by
      simpa [locOnly, Bool.and_eq_true] using h
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact locFrame_eval no h12.2 s
      · exact locFrame_eval yes h12.1 s
    · exact LocFrame.refl s
  | .while _ _, h, _ => by simp [locOnly] at h
  | .call _ _ _, h, _ => by simp [locOnly] at h
  | .decCall _ _ _ _ _, h, _ => by simp [locOnly] at h
  | .store _ _, h, _ => by simp [locOnly] at h
  | .storeByte _ _, h, _ => by simp [locOnly] at h
  | .store32 _ _, h, _ => by simp [locOnly] at h
  | .tick, h, _ => by simp [locOnly] at h
  | .primitive _ _ _, h, _ => by simp [locOnly] at h
  | .extCall _ _ _ _ _, h, _ => by simp [locOnly] at h
  | .shMemLoad _ _ _ _, h, _ => by simp [locOnly] at h
  | .shMemStore _ _ _, h, _ => by simp [locOnly] at h

/-- Reduce the structural translation of a guest function body. -/
macro "htab_unfold" d:ident : tactic => `(tactic| dsimp only [extractFn, $d:ident,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map])

end InitECandidate.Solver.Wave8HtabAstra.Htab

/-! Source: Exit.lean; Opus port from 3ea193df0. -/

/-! The table-exit relation `HtabExit` for an explicit table address, reflexive and transitive,
so that the loops of `htab_truncate` / `htab_union_into` compose it over iterations. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace InitECandidate.Solver.Wave8HtabAstra.Htab

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.Wave8HtabAstra

def ExitR {F : Type} (t : Nat) (s post : PanSemStateFiniteExact 64 F) : Prop :=
  let fresh : Ivl := (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr")
  ArenaReady post ∧ HtabWF post t ∧
  globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
  (∀ i ∈ htabFootprint post t, Allocated post i ∧
    ((∃ j ∈ htabFootprint s t, Inside i j.1 (j.1 + j.2)) ∨ Inside i fresh.1 (fresh.1 + fresh.2))) ∧
  FrameOutside s post (htabFootprint s t) fresh ∧
  (∀ name, name ≠ "heap_ptr" → s.globals.lookup (ofString name) = post.globals.lookup (ofString name))

theorem htabExit_iff {F : Type} (s post : PanSemStateFiniteExact 64 F) :
    HtabExit s post ↔ ExitR (locN s "t") s post := Iff.rfl

theorem ExitR.refl {F : Type} (t : Nat) (s : PanSemStateFiniteExact 64 F) (hA : ArenaReady s)
    (hW : HtabWF s t) (hal : ∀ i ∈ htabFootprint s t, Allocated s i) : ExitR t s s := by
  refine ⟨hA, hW, le_refl _, fun i hi => ⟨hal i hi, Or.inl ⟨i, hi, le_refl _, le_refl _⟩⟩,
    fun _ _ _ => rfl, fun _ _ => rfl⟩

theorem exitR_locals {F : Type} (t : Nat) (a b : PanSemStateFiniteExact 64 F)
    (L1 L2 : HolFiniteMapExact MlS (ValueHOL 64)) (k1 k2 : Nat) :
    ExitR t { a with locals := L1, clock := k1 } { b with locals := L2, clock := k2 } ↔
      ExitR t a b := by
  simp only [ExitR, arenaReady_with_locals, htabWF_with_locals]
  exact Iff.rfl

end InitECandidate.Solver.Wave8HtabAstra.Htab

/-! Source: Truncate.lean; Opus port from 3ea193df0. -/

/-! `gb_htab_truncate` (guard `HtabArgWF`): `while n <+ count { htab_del(t, key of the last
leaf) }` with `while_rank_stationary`, `μ = count (t+24) < 2^64`. Each continuing iteration
returns from `htab_del`, so `htab_del_spec` keeps `HtabArgWF` and `htab_del_progress_spec` either
lowers the count or makes the next loop head an exact repeat (`SameHead`).

The two contract leaves and `fb_memeq` (bytes family) are hypotheses. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8HtabAstra.Htab

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8HtabAstra

/-! ### Callee parameters (copied from `GuestBoundCryptoPrecompiles`, not on this cone) -/

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


/-! ### Semantics of `dec` and of a call without destination, on flowing runs -/

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

/-! ### One iteration of the `htab_truncate` loop body -/

abbrev HtabDelSpec : Prop := FunSpec HtabArgWF (OnReturn HtabExit) (ofString "htab_del")
abbrev HtabDelProgressSpec : Prop :=
  FunSpec HtabArgWF (OnReturn HtabDelProgress) (ofString "htab_del")

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


end InitECandidate.Solver.Wave8HtabAstra.Htab

/-! Source: Inv.lean; Opus port from 3ea193df0. -/

/-! Invariant rule for the normal completion of a `while` loop: if every completed iteration
(`none`, `continue` or `break`) from an `I` head lands in `I`, a normally completed loop ends
in `I`. By induction on the clock. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace InitECandidate.Solver.Wave8HtabAstra.Htab

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8HtabAstra

theorem while_inv {F : Type} (I : PanSemStateFiniteExact 64 F → Prop) (cond : ExpHOL 64)
    (body : ProgHOL 64)
    (hstep : ∀ s : PanSemStateFiniteExact 64 F, I s → s.clock ≠ 0 →
      ((evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none ∨
        (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = some .continue ∨
        (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = some .break) →
      I (evaluateHOLFiniteState (decClockHOLFinite s) body).2) :
    ∀ (n : Nat) (s : PanSemStateFiniteExact 64 F), s.clock ≤ n → I s →
      (evaluateHOLFiniteState s (.while cond body)).1 = none →
      I (evaluateHOLFiniteState s (.while cond body)).2 := by
  intro n
  induction n with
  | zero =>
    intro s hcl hs hnone
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnone ⊢
    revert hnone
    split
    · rename_i w hw
      by_cases hz : w = 0
      · simp [hz]; exact hs
      · rw [if_pos hz]
        rw [if_pos (by omega)]
        simp
    · simp
  | succ n ih =>
    intro s hcl hs hnone
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnone ⊢
    revert hnone
    split
    · rename_i w hw
      by_cases hz : w = 0
      · simp [hz]; exact hs
      · rw [if_pos hz]
        by_cases hc : s.clock = 0
        · rw [if_pos hc]; simp
        · rw [if_neg hc]
          have hle := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          rcases hb : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r, t⟩
          rw [hb] at hle
          change t.clock ≤ s.clock - 1 at hle
          have hI : (r = none ∨ r = some .continue ∨ r = some .break) → I t := by
            intro hr
            have := hstep s hs hc (by rw [hb]; exact hr)
            rw [hb] at this
            exact this
          dsimp only
          rcases r with _ | r
          · intro hn
            exact ih t (by omega) (hI (Or.inl rfl)) hn
          · cases r with
            | «continue» =>
              intro hn
              exact ih t (by omega) (hI (Or.inr (Or.inl rfl))) hn
            | «break» =>
              intro _
              exact hI (Or.inr (Or.inr rfl))
            | _ => simp
    · simp

theorem while_inv_act {F : Type} (I : PanSemStateFiniteExact 64 F → Prop) (cond : ExpHOL 64)
    (body : ProgHOL 64)
    (hstep : ∀ s : PanSemStateFiniteExact 64 F, I s → LoopActive cond s → s.clock ≠ 0 →
      ((evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none ∨
        (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = some .continue ∨
        (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = some .break) →
      I (evaluateHOLFiniteState (decClockHOLFinite s) body).2) :
    ∀ (n : Nat) (s : PanSemStateFiniteExact 64 F), s.clock ≤ n → I s →
      (evaluateHOLFiniteState s (.while cond body)).1 = none →
      I (evaluateHOLFiniteState s (.while cond body)).2 := by
  intro n
  induction n with
  | zero =>
    intro s hcl hs hnone
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnone ⊢
    revert hnone
    split
    · rename_i w hw
      by_cases hz : w = 0
      · simp [hz]; exact hs
      · rw [if_pos hz]
        rw [if_pos (by omega)]
        simp
    · simp
  | succ n ih =>
    intro s hcl hs hnone
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnone ⊢
    revert hnone
    split
    · rename_i w hw
      by_cases hz : w = 0
      · simp [hz]; exact hs
      · rw [if_pos hz]
        by_cases hc : s.clock = 0
        · rw [if_pos hc]; simp
        · rw [if_neg hc]
          have hle := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          rcases hb : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r, t⟩
          rw [hb] at hle
          change t.clock ≤ s.clock - 1 at hle
          have hI : (r = none ∨ r = some .continue ∨ r = some .break) → I t := by
            intro hr
            have := hstep s hs ⟨w, hw, hz⟩ hc (by rw [hb]; exact hr)
            rw [hb] at this
            exact this
          dsimp only
          rcases r with _ | r
          · intro hn
            exact ih t (by omega) (hI (Or.inl rfl)) hn
          · cases r with
            | «continue» =>
              intro hn
              exact ih t (by omega) (hI (Or.inr (Or.inl rfl))) hn
            | «break» =>
              intro _
              exact hI (Or.inr (Or.inr rfl))
            | _ => simp
    · simp

end InitECandidate.Solver.Wave8HtabAstra.Htab

namespace InitECandidate.Solver.Wave8HtabAstra.Htab

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8HtabAstra

/-- A result that a loop body may produce without making the loop return or break out. -/
def NoRetBrk (r : Option (PanSemResultExact 64)) : Prop :=
  (∀ v, r ≠ some (.returned v)) ∧ r ≠ some .break

theorem call0_noRetBrk {F : Type} (s : PanSemStateFiniteExact 64 F) (f : MlS)
    (args : List (ExpHOL 64)) :
    NoRetBrk (evaluateHOLFiniteState s (.call (some (none, none)) f args)).1 ∧
      (evaluateHOLFiniteState s (.call (some (none, none)) f args)).1 ≠ some .continue := by
  rw [evaluateHOLFiniteState_call]
  split
  · simp [NoRetBrk]
  · split
    · simp [NoRetBrk]
    · split
      · simp [NoRetBrk]
      · rcases evaluateHOLFiniteState (callEntryStateHOLFinite s _) _ with ⟨r, t⟩
        rcases r with _ | r
        · simp [NoRetBrk]
        · cases r with
          | returned v =>
            dsimp only
            split <;> simp [NoRetBrk]
          | exception _ _ => simp [NoRetBrk]
          | _ => simp [NoRetBrk]

theorem dec_res {F : Type} (s : PanSemStateFiniteExact 64 F) (x : MlS) (sh : ShapeHOL)
    (e : ExpHOL 64) (p : ProgHOL 64) :
    (evaluateHOLFiniteState s (.dec x sh e p)).1 = some .error ∨
      ∃ v, (evaluateHOLFiniteState s (.dec x sh e p)).1 =
        (evaluateHOLFiniteState (setVarHOLFinite x v s) p).1 := by
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  split
  · simp
  · rename_i v _
    split
    · exact Or.inr ⟨v, rfl⟩
    · simp

/-- `dec a (dec b (call f args))` never returns, breaks or continues. -/
theorem dec2call_res {F : Type} (s : PanSemStateFiniteExact 64 F) (a b f : MlS)
    (sa sb : ShapeHOL) (e1 e2 : ExpHOL 64) (args : List (ExpHOL 64)) :
    let r := (evaluateHOLFiniteState s
      (.dec a sa e1 (.dec b sb e2 (.call (some (none, none)) f args)))).1
    NoRetBrk r ∧ r ≠ some .continue := by
  intro r
  rcases dec_res s a sa e1 _ with h | ⟨v, h⟩
  · have hr : r = some .error := h
    rw [hr]; simp [NoRetBrk]
  · rcases dec_res (setVarHOLFinite a v s) b sb e2 _ with h' | ⟨w, h'⟩
    · have hr : r = some .error := h.trans h'
      rw [hr]; simp [NoRetBrk]
    · have hr : r = _ := h.trans h'
      rw [hr]; exact call0_noRetBrk _ _ _

theorem while_noRet {F : Type} (cond : ExpHOL 64) (body : ProgHOL 64)
    (hb : ∀ s : PanSemStateFiniteExact 64 F, ∀ v,
      (evaluateHOLFiniteState s body).1 ≠ some (.returned v)) :
    ∀ (n : Nat) (s : PanSemStateFiniteExact 64 F), s.clock ≤ n → ∀ v,
      (evaluateHOLFiniteState s (.while cond body)).1 ≠ some (.returned v) := by
  intro n
  induction n with
  | zero =>
    intro s hcl v
    rw [evaluateHOLFiniteState_while_fixClockRewrite]
    split
    · rename_i w hw
      by_cases hz : w = 0
      · simp [hz]
      · rw [if_pos hz, if_pos (by omega)]; simp
    · simp
  | succ n ih =>
    intro s hcl v
    rw [evaluateHOLFiniteState_while_fixClockRewrite]
    split
    · rename_i w hw
      by_cases hz : w = 0
      · simp [hz]
      · rw [if_pos hz]
        by_cases hc : s.clock = 0
        · rw [if_pos hc]; simp
        · rw [if_neg hc]
          have hle := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          have hbv := hb (decClockHOLFinite s) v
          rcases hbd : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r, t⟩
          rw [hbd] at hle hbv
          change t.clock ≤ s.clock - 1 at hle
          dsimp only at hbv ⊢
          rcases r with _ | r
          · exact ih t (by omega) v
          · cases r with
            | «continue» => exact ih t (by omega) v
            | «break» => simp
            | returned v' => exact hbv
            | _ => simp
    · simp

end InitECandidate.Solver.Wave8HtabAstra.Htab

namespace InitECandidate.Solver.Wave8HtabAstra.Htab
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8HtabAstra

/-- Invariant rule distinguishing the two normal exits of a loop: the test fails (in an `I`
state), or the body breaks (in a `Bk` state). -/
theorem while_inv2 {F : Type} (I Bk : PanSemStateFiniteExact 64 F → Prop) (cond : ExpHOL 64)
    (body : ProgHOL 64)
    (hstep : ∀ s : PanSemStateFiniteExact 64 F, I s → LoopActive cond s → s.clock ≠ 0 →
      (((evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none ∨
        (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = some .continue) →
        I (evaluateHOLFiniteState (decClockHOLFinite s) body).2) ∧
      ((evaluateHOLFiniteState (decClockHOLFinite s) body).1 = some .break →
        Bk (evaluateHOLFiniteState (decClockHOLFinite s) body).2)) :
    ∀ (n : Nat) (s : PanSemStateFiniteExact 64 F), s.clock ≤ n → I s →
      (evaluateHOLFiniteState s (.while cond body)).1 = none →
      (I (evaluateHOLFiniteState s (.while cond body)).2 ∧
        CondFalse cond (evaluateHOLFiniteState s (.while cond body)).2) ∨
      Bk (evaluateHOLFiniteState s (.while cond body)).2 := by
  intro n
  induction n with
  | zero =>
    intro s hcl hs hnone
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnone ⊢
    revert hnone
    split
    · rename_i w hw
      by_cases hz : w = 0
      · subst hz; simp; exact Or.inl ⟨hs, hw⟩
      · rw [if_pos hz]
        rw [if_pos (by omega)]
        simp
    · simp
  | succ n ih =>
    intro s hcl hs hnone
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnone ⊢
    revert hnone
    split
    · rename_i w hw
      by_cases hz : w = 0
      · subst hz; simp; exact Or.inl ⟨hs, hw⟩
      · rw [if_pos hz]
        by_cases hc : s.clock = 0
        · rw [if_pos hc]; simp
        · rw [if_neg hc]
          have hle := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          have hst := hstep s hs ⟨w, hw, hz⟩ hc
          rcases hb : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r, t⟩
          rw [hb] at hle hst
          change t.clock ≤ s.clock - 1 at hle
          dsimp only at hst ⊢
          rcases r with _ | r
          · intro hn
            exact ih t (by omega) (hst.1 (Or.inl rfl)) hn
          · cases r with
            | «continue» =>
              intro hn
              exact ih t (by omega) (hst.1 (Or.inr rfl)) hn
            | «break» =>
              intro _
              exact Or.inr (hst.2 rfl)
            | _ => simp
    · simp

end InitECandidate.Solver.Wave8HtabAstra.Htab

/-! Source: Ret.lean; Opus port from 3ea193df0. -/

/-! Rules for reasoning about the NORMAL RETURN of a loop-free body from one fixed state:
`Ret s p Φ` says that if `p` returns `v` from `s`, the final state satisfies `Φ v`.
`Φ` may mention `s` (and any entry state) directly, so relational exits (`FrameOutside`)
are stated without ghost encodings. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace InitECandidate.Solver.Wave8HtabAstra.Htab

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanRunBounded

def Ret {F : Type} (s : PanSemStateFiniteExact 64 F) (p : ProgHOL 64)
    (Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop) : Prop :=
  ∀ v, (evaluateHOLFiniteState s p).1 = some (.returned v) → Φ v (evaluateHOLFiniteState s p).2

/-- Expression evaluation at a state. -/
noncomputable abbrev ev {F : Type} (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) :
    Option (ValueHOL 64) :=
  @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e

theorem Ret.seq {F : Type} {s : PanSemStateFiniteExact 64 F} {a b : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (ha : Ret s a Φ) (hb : ∀ t, evaluateHOLFiniteState s a = (none, t) → Ret t b Φ) :
    Ret s (.seq a b) Φ := by
  intro v hv
  rw [evaluateHOLFiniteState_seq_line780] at hv ⊢
  rcases h : evaluateHOLFiniteState s a with ⟨r, t⟩
  simp only [h] at hv
  try simp only [h]
  cases r with
  | none => exact hb t h v hv
  | some r' =>
    have := ha v (by rw [h]; exact hv)
    rw [h] at this
    exact this

/-- A store never returns; on success it updates memory. -/
theorem Ret.seq_store {F : Type} {s : PanSemStateFiniteExact 64 F} {d e : ExpHOL 64}
    {b : ProgHOL 64} {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hb : ∀ (a : BitVec 64) (val : ValueHOL 64) m, ev s d = some (.val (.word a)) →
      ev s e = some val →
      @panMemStoresHOL 64 _ a (flattenHOL val) s.memaddrs
        (fun x => Classical.propDecidable (s.memaddrs x)) s.memory = some m →
      Ret { s with memory := m } b Φ) :
    Ret s (.seq (.store d e) b) Φ := by
  refine Ret.seq ?_ ?_
  · intro v hv
    rw [evaluateHOLFiniteState_store] at hv
    revert hv
    split
    · split
      · split <;> simp
      · simp
    · simp
  · intro t ht
    rw [evaluateHOLFiniteState_store] at ht
    revert ht
    split
    · rename_i a hd
      split
      · rename_i val he
        split
        · rename_i m hm
          intro ht
          simp only [Prod.mk.injEq] at ht
          rw [← ht.2]
          exact hb a val m hd he hm
        · simp
      · simp
    · simp

theorem Ret.dec {F : Type} {s : PanSemStateFiniteExact 64 F} {x : MlS} {sh : ShapeHOL}
    {init : ExpHOL 64} {body : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (h : ∀ val, ev s init = some val →
      Ret (setVarHOLFinite x val s) body
        (fun v t => Φ v { t with
          locals := HolFiniteMapExact.resVarEq t.locals (x, s.locals.lookup x) })) :
    Ret s (.dec x sh init body) Φ := by
  intro v hv
  rw [evaluateHOLFiniteState_dec_total] at hv ⊢
  dsimp only at hv ⊢
  revert hv
  split
  · simp
  · rename_i val hval
    split
    · intro hv
      exact h val hval v hv
    · simp

theorem Ret.ret {F : Type} {s : PanSemStateFiniteExact 64 F} {e : ExpHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (h : ∀ val, ev s e = some val → Φ val (emptyLocalsHOLFinite s)) :
    Ret s (.return e) Φ := by
  intro v hv
  rw [evaluateHOLFiniteState_return] at hv ⊢
  revert hv
  split
  · simp
  · rename_i val hval
    split
    · intro hv
      simp only [Option.some.injEq, PanSemResultExact.returned.injEq] at hv
      subst hv
      exact h _ hval
    · simp

/-- `ite` whose test is known false, followed by the rest. -/
theorem Ret.seq_ite_false {F : Type} {s : PanSemStateFiniteExact 64 F} {c : ExpHOL 64}
    {y n b : ProgHOL 64} {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hc : ev s c = some (.val (.word 0))) (hn : Ret s (.seq n b) Φ) :
    Ret s (.seq (.ite c y n) b) Φ := by
  have : evaluateHOLFiniteState s (.ite c y n) = evaluateHOLFiniteState s n := by
    rw [evaluateHOLFiniteState_ite]
    simp only [ev] at hc
    rw [hc]
    simp
  intro v hv
  rw [evaluateHOLFiniteState_seq_line780, this] at hv ⊢
  have := hn v (by rw [evaluateHOLFiniteState_seq_line780]; exact hv)
  rw [evaluateHOLFiniteState_seq_line780] at this
  exact this

/-- `decCall x alloc-like [arg] cont`: the callee has one word parameter `n`. -/
theorem Ret.decCall1 {F : Type} {s : PanSemStateFiniteExact 64 F} {x fname : MlS}
    {arg : ExpHOL 64} {cont fbody : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hcode : s.code = originalRuntimeCode)
    (hlook : originalRuntimeCode.lookup fname = some ([(ofString "n", .one)], fbody, .one))
    (nv : BitVec 64) (harg : ev s arg = some (.val (.word nv)))
    (hk : ∀ w post,
      evaluateHOLFiniteState
        (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n", .val (.word nv))))
        fbody = (some (.returned (.val (.word w))), post) →
      Ret (setVarHOLFinite x (.val (.word w)) { post with locals := s.locals }) cont
        (fun v t => Φ v { t with
          locals := HolFiniteMapExact.resVarEq t.locals (x, s.locals.lookup x) })) :
    Ret s (.decCall x .one fname [arg] cont) Φ := by
  intro v hv
  rw [evaluateHOLFiniteState_decCall_total] at hv ⊢
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [arg] =
      some [.val (.word nv)] := by
    simp only [ev] at harg
    simp [evalListHOLFinite, evalListHOLExact, harg]
  have hl := pan_one_word_lookup s.code.lookup fname (ofString "n") fbody nv
    (by rw [hcode]; exact hlook)
  rw [hargs] at hv ⊢
  dsimp only at hv ⊢
  rw [hl] at hv ⊢
  dsimp only at hv ⊢
  revert hv
  split
  · simp
  · rw [fixClockHOLFinite_evaluateState]
    rcases hrun : evaluateHOLFiniteState
        (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n", .val (.word nv))))
        fbody with ⟨r, post⟩
    dsimp only
    rcases r with _ | r
    · simp
    · cases r with
      | returned rv =>
        dsimp only
        split
        · rename_i hsh
          rcases rv with ⟨⟨w⟩⟩ | fs | ⟨nm, fs⟩
          · intro hv
            exact hk w post hrun v hv
          · simp [shapeOfHOLExact, shapeEqHOL] at hsh
          · simp [shapeOfHOLExact, shapeEqHOL] at hsh
        · simp
      | _ => simp

def updW (m : BitVec 64 → HolWordLab 64) (a w : BitVec 64) : BitVec 64 → HolWordLab 64 :=
  fun c => if c = a then .word w else m c

theorem stores_word {dom : BitVec 64 → Prop} (inst : DecidablePred dom)
    {m m' : BitVec 64 → HolWordLab 64}
    {a w : BitVec 64} (h : @panMemStoresHOL 64 _ a (flattenHOL (.val (.word w))) dom inst m = some m') :
    dom a ∧ m' = updW m a w := by
  unfold flattenHOL at h
  unfold panMemStoresHOL at h
  unfold panMemStoreHOL at h
  by_cases hd : dom a
  · simp only [hd, ↓reduceIte] at h
    simp only [panMemStoresHOL, Option.some.injEq] at h
    exact ⟨hd, h.symm⟩
  · simp [hd] at h

/-- A word store `st e1, e2` (both words) followed by the rest. -/
theorem Ret.seq_storeW {F : Type} {s : PanSemStateFiniteExact 64 F} {d e : ExpHOL 64}
    {b : ProgHOL 64} {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (a w : BitVec 64) (hd : ev s d = some (.val (.word a))) (he : ev s e = some (.val (.word w)))
    (hb : s.memaddrs a → Ret { s with memory := updW s.memory a w } b Φ) :
    Ret s (.seq (.store d e) b) Φ := by
  apply Ret.seq_store
  intro a' val m hd' he' hm
  rw [hd] at hd'
  rw [he] at he'
  simp only [Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hd' he'
  subst hd' he'
  obtain ⟨hdom, rfl⟩ := stores_word _ hm
  exact hb hdom

theorem Ret.skip_noret {F : Type} {s : PanSemStateFiniteExact 64 F}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop} : Ret s .skip Φ := by
  intro v hv
  rw [evaluateHOLFiniteState_skip] at hv
  cases hv

/-! ### Normal-form states: the entry state with new locals, globals, memory and clock.
Every step below maps a normal-form state to a normal-form state, so the state terms stay
small. -/

def NS {F : Type} (s : PanSemStateFiniteExact 64 F) (L G : HolFiniteMapExact MlS (ValueHOL 64))
    (M : BitVec 64 → HolWordLab 64) (C : Nat) : PanSemStateFiniteExact 64 F :=
  { s with locals := L, globals := G, memory := M, clock := C }

section NSlemmas
variable {F : Type} (s : PanSemStateFiniteExact 64 F) (L G : HolFiniteMapExact MlS (ValueHOL 64))
  (M : BitVec 64 → HolWordLab 64) (C : Nat)
@[simp] theorem NS_locals : (NS s L G M C).locals = L := rfl
@[simp] theorem NS_globals : (NS s L G M C).globals = G := rfl
@[simp] theorem NS_memory : (NS s L G M C).memory = M := rfl
@[simp] theorem NS_clock : (NS s L G M C).clock = C := rfl
@[simp] theorem NS_code : (NS s L G M C).code = s.code := rfl
@[simp] theorem NS_memaddrs : (NS s L G M C).memaddrs = s.memaddrs := rfl
@[simp] theorem NS_toExact_memaddrs : (NS s L G M C).toExact.memaddrs = s.memaddrs := rfl
end NSlemmas

theorem Ret.of_NS {F : Type} {s : PanSemStateFiniteExact 64 F} {p : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (h : Ret (NS s s.locals s.globals s.memory s.clock) p Φ) : Ret s p Φ := by
  cases s; exact h

theorem Ret.ns_storeW {F : Type} {s : PanSemStateFiniteExact 64 F} {L G} {M C}
    {d e : ExpHOL 64} {b : ProgHOL 64} {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (a w : BitVec 64) (hd : ev (NS s L G M C) d = some (.val (.word a)))
    (he : ev (NS s L G M C) e = some (.val (.word w)))
    (hb : s.memaddrs a → Ret (NS s L G (updW M a w) C) b Φ) :
    Ret (NS s L G M C) (.seq (.store d e) b) Φ :=
  Ret.seq_storeW a w hd he hb

theorem Ret.ns_dec {F : Type} {s : PanSemStateFiniteExact 64 F} {L G} {M C} {x : MlS}
    {sh : ShapeHOL} {init : ExpHOL 64} {body : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (h : ∀ val, ev (NS s L G M C) init = some val →
      Ret (NS s (L.update (x, val)) G M C) body
        (fun v t => Φ v { t with locals := HolFiniteMapExact.resVarEq t.locals (x, L.lookup x) })) :
    Ret (NS s L G M C) (.dec x sh init body) Φ :=
  Ret.dec h

theorem Ret.ns_ret {F : Type} {s : PanSemStateFiniteExact 64 F} {L G} {M C} {e : ExpHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (h : ∀ val, ev (NS s L G M C) e = some val →
      Φ val (NS s (emptyLocalsHOLFinite (NS s L G M C)).locals G M C)) :
    Ret (NS s L G M C) (.return e) Φ :=
  Ret.ret h

theorem Ret.ns_ite_false_skip {F : Type} {s : PanSemStateFiniteExact 64 F} {L G} {M C}
    {c : ExpHOL 64} {y b : ProgHOL 64} {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hc : ev (NS s L G M C) c = some (.val (.word 0))) (hb : Ret (NS s L G M C) b Φ) :
    Ret (NS s L G M C) (.seq (.ite c y .skip) b) Φ := by
  refine Ret.seq_ite_false hc (Ret.seq Ret.skip_noret ?_)
  intro t ht
  rw [evaluateHOLFiniteState_skip] at ht
  cases ht
  exact hb

end InitECandidate.Solver.Wave8HtabAstra.Htab

/-! Source: Names.lean; Opus port from 3ea193df0. -/

/-! Distinctness of the local and global names used by the table functions (`decide`). -/

namespace InitECandidate.Solver.Wave8HtabAstra.Htab
open Flapjack.Basis.Pure.MlString

@[simp] theorem nm_t_stride : (ofString "t" = ofString "stride") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_t_keys : (ofString "t" = ofString "keys") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_t_nodes : (ofString "t" = ofString "nodes") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_t_n : (ofString "t" = ofString "n") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_t_p : (ofString "t" = ofString "p") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_t_b : (ofString "t" = ofString "b") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_t_keybits : (ofString "t" = ofString "keybits") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_t_key : (ofString "t" = ofString "key") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_t_leaf : (ofString "t" = ofString "leaf") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_t_klen : (ofString "t" = ofString "klen") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_t_eq : (ofString "t" = ofString "eq") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_t_pos : (ofString "t" = ofString "pos") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_t_count : (ofString "t" = ofString "count") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_t_g : (ofString "t" = ofString "g") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_t_s : (ofString "t" = ofString "s") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_stride_t : (ofString "stride" = ofString "t") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_stride_keys : (ofString "stride" = ofString "keys") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_stride_nodes : (ofString "stride" = ofString "nodes") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_stride_n : (ofString "stride" = ofString "n") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_stride_p : (ofString "stride" = ofString "p") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_stride_b : (ofString "stride" = ofString "b") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_stride_keybits : (ofString "stride" = ofString "keybits") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_stride_key : (ofString "stride" = ofString "key") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_stride_leaf : (ofString "stride" = ofString "leaf") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_stride_klen : (ofString "stride" = ofString "klen") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_stride_eq : (ofString "stride" = ofString "eq") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_stride_pos : (ofString "stride" = ofString "pos") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_stride_count : (ofString "stride" = ofString "count") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_stride_g : (ofString "stride" = ofString "g") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_stride_s : (ofString "stride" = ofString "s") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_keys_t : (ofString "keys" = ofString "t") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_keys_stride : (ofString "keys" = ofString "stride") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_keys_nodes : (ofString "keys" = ofString "nodes") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_keys_n : (ofString "keys" = ofString "n") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_keys_p : (ofString "keys" = ofString "p") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_keys_b : (ofString "keys" = ofString "b") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_keys_keybits : (ofString "keys" = ofString "keybits") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_keys_key : (ofString "keys" = ofString "key") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_keys_leaf : (ofString "keys" = ofString "leaf") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_keys_klen : (ofString "keys" = ofString "klen") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_keys_eq : (ofString "keys" = ofString "eq") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_keys_pos : (ofString "keys" = ofString "pos") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_keys_count : (ofString "keys" = ofString "count") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_keys_g : (ofString "keys" = ofString "g") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_keys_s : (ofString "keys" = ofString "s") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_nodes_t : (ofString "nodes" = ofString "t") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_nodes_stride : (ofString "nodes" = ofString "stride") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_nodes_keys : (ofString "nodes" = ofString "keys") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_nodes_n : (ofString "nodes" = ofString "n") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_nodes_p : (ofString "nodes" = ofString "p") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_nodes_b : (ofString "nodes" = ofString "b") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_nodes_keybits : (ofString "nodes" = ofString "keybits") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_nodes_key : (ofString "nodes" = ofString "key") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_nodes_leaf : (ofString "nodes" = ofString "leaf") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_nodes_klen : (ofString "nodes" = ofString "klen") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_nodes_eq : (ofString "nodes" = ofString "eq") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_nodes_pos : (ofString "nodes" = ofString "pos") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_nodes_count : (ofString "nodes" = ofString "count") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_nodes_g : (ofString "nodes" = ofString "g") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_nodes_s : (ofString "nodes" = ofString "s") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_n_t : (ofString "n" = ofString "t") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_n_stride : (ofString "n" = ofString "stride") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_n_keys : (ofString "n" = ofString "keys") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_n_nodes : (ofString "n" = ofString "nodes") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_n_p : (ofString "n" = ofString "p") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_n_b : (ofString "n" = ofString "b") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_n_keybits : (ofString "n" = ofString "keybits") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_n_key : (ofString "n" = ofString "key") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_n_leaf : (ofString "n" = ofString "leaf") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_n_klen : (ofString "n" = ofString "klen") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_n_eq : (ofString "n" = ofString "eq") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_n_pos : (ofString "n" = ofString "pos") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_n_count : (ofString "n" = ofString "count") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_n_g : (ofString "n" = ofString "g") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_n_s : (ofString "n" = ofString "s") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_p_t : (ofString "p" = ofString "t") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_p_stride : (ofString "p" = ofString "stride") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_p_keys : (ofString "p" = ofString "keys") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_p_nodes : (ofString "p" = ofString "nodes") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_p_n : (ofString "p" = ofString "n") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_p_b : (ofString "p" = ofString "b") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_p_keybits : (ofString "p" = ofString "keybits") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_p_key : (ofString "p" = ofString "key") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_p_leaf : (ofString "p" = ofString "leaf") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_p_klen : (ofString "p" = ofString "klen") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_p_eq : (ofString "p" = ofString "eq") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_p_pos : (ofString "p" = ofString "pos") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_p_count : (ofString "p" = ofString "count") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_p_g : (ofString "p" = ofString "g") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_p_s : (ofString "p" = ofString "s") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_b_t : (ofString "b" = ofString "t") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_b_stride : (ofString "b" = ofString "stride") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_b_keys : (ofString "b" = ofString "keys") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_b_nodes : (ofString "b" = ofString "nodes") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_b_n : (ofString "b" = ofString "n") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_b_p : (ofString "b" = ofString "p") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_b_keybits : (ofString "b" = ofString "keybits") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_b_key : (ofString "b" = ofString "key") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_b_leaf : (ofString "b" = ofString "leaf") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_b_klen : (ofString "b" = ofString "klen") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_b_eq : (ofString "b" = ofString "eq") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_b_pos : (ofString "b" = ofString "pos") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_b_count : (ofString "b" = ofString "count") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_b_g : (ofString "b" = ofString "g") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_b_s : (ofString "b" = ofString "s") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_keybits_t : (ofString "keybits" = ofString "t") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_keybits_stride : (ofString "keybits" = ofString "stride") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_keybits_keys : (ofString "keybits" = ofString "keys") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_keybits_nodes : (ofString "keybits" = ofString "nodes") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_keybits_n : (ofString "keybits" = ofString "n") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_keybits_p : (ofString "keybits" = ofString "p") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_keybits_b : (ofString "keybits" = ofString "b") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_keybits_key : (ofString "keybits" = ofString "key") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_keybits_leaf : (ofString "keybits" = ofString "leaf") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_keybits_klen : (ofString "keybits" = ofString "klen") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_keybits_eq : (ofString "keybits" = ofString "eq") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_keybits_pos : (ofString "keybits" = ofString "pos") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_keybits_count : (ofString "keybits" = ofString "count") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_keybits_g : (ofString "keybits" = ofString "g") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_keybits_s : (ofString "keybits" = ofString "s") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_key_t : (ofString "key" = ofString "t") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_key_stride : (ofString "key" = ofString "stride") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_key_keys : (ofString "key" = ofString "keys") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_key_nodes : (ofString "key" = ofString "nodes") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_key_n : (ofString "key" = ofString "n") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_key_p : (ofString "key" = ofString "p") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_key_b : (ofString "key" = ofString "b") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_key_keybits : (ofString "key" = ofString "keybits") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_key_leaf : (ofString "key" = ofString "leaf") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_key_klen : (ofString "key" = ofString "klen") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_key_eq : (ofString "key" = ofString "eq") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_key_pos : (ofString "key" = ofString "pos") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_key_count : (ofString "key" = ofString "count") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_key_g : (ofString "key" = ofString "g") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_key_s : (ofString "key" = ofString "s") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_leaf_t : (ofString "leaf" = ofString "t") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_leaf_stride : (ofString "leaf" = ofString "stride") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_leaf_keys : (ofString "leaf" = ofString "keys") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_leaf_nodes : (ofString "leaf" = ofString "nodes") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_leaf_n : (ofString "leaf" = ofString "n") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_leaf_p : (ofString "leaf" = ofString "p") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_leaf_b : (ofString "leaf" = ofString "b") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_leaf_keybits : (ofString "leaf" = ofString "keybits") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_leaf_key : (ofString "leaf" = ofString "key") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_leaf_klen : (ofString "leaf" = ofString "klen") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_leaf_eq : (ofString "leaf" = ofString "eq") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_leaf_pos : (ofString "leaf" = ofString "pos") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_leaf_count : (ofString "leaf" = ofString "count") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_leaf_g : (ofString "leaf" = ofString "g") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_leaf_s : (ofString "leaf" = ofString "s") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_klen_t : (ofString "klen" = ofString "t") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_klen_stride : (ofString "klen" = ofString "stride") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_klen_keys : (ofString "klen" = ofString "keys") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_klen_nodes : (ofString "klen" = ofString "nodes") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_klen_n : (ofString "klen" = ofString "n") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_klen_p : (ofString "klen" = ofString "p") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_klen_b : (ofString "klen" = ofString "b") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_klen_keybits : (ofString "klen" = ofString "keybits") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_klen_key : (ofString "klen" = ofString "key") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_klen_leaf : (ofString "klen" = ofString "leaf") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_klen_eq : (ofString "klen" = ofString "eq") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_klen_pos : (ofString "klen" = ofString "pos") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_klen_count : (ofString "klen" = ofString "count") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_klen_g : (ofString "klen" = ofString "g") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_klen_s : (ofString "klen" = ofString "s") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_eq_t : (ofString "eq" = ofString "t") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_eq_stride : (ofString "eq" = ofString "stride") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_eq_keys : (ofString "eq" = ofString "keys") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_eq_nodes : (ofString "eq" = ofString "nodes") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_eq_n : (ofString "eq" = ofString "n") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_eq_p : (ofString "eq" = ofString "p") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_eq_b : (ofString "eq" = ofString "b") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_eq_keybits : (ofString "eq" = ofString "keybits") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_eq_key : (ofString "eq" = ofString "key") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_eq_leaf : (ofString "eq" = ofString "leaf") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_eq_klen : (ofString "eq" = ofString "klen") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_eq_pos : (ofString "eq" = ofString "pos") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_eq_count : (ofString "eq" = ofString "count") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_eq_g : (ofString "eq" = ofString "g") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_eq_s : (ofString "eq" = ofString "s") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_pos_t : (ofString "pos" = ofString "t") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_pos_stride : (ofString "pos" = ofString "stride") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_pos_keys : (ofString "pos" = ofString "keys") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_pos_nodes : (ofString "pos" = ofString "nodes") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_pos_n : (ofString "pos" = ofString "n") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_pos_p : (ofString "pos" = ofString "p") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_pos_b : (ofString "pos" = ofString "b") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_pos_keybits : (ofString "pos" = ofString "keybits") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_pos_key : (ofString "pos" = ofString "key") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_pos_leaf : (ofString "pos" = ofString "leaf") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_pos_klen : (ofString "pos" = ofString "klen") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_pos_eq : (ofString "pos" = ofString "eq") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_pos_count : (ofString "pos" = ofString "count") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_pos_g : (ofString "pos" = ofString "g") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_pos_s : (ofString "pos" = ofString "s") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_count_t : (ofString "count" = ofString "t") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_count_stride : (ofString "count" = ofString "stride") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_count_keys : (ofString "count" = ofString "keys") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_count_nodes : (ofString "count" = ofString "nodes") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_count_n : (ofString "count" = ofString "n") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_count_p : (ofString "count" = ofString "p") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_count_b : (ofString "count" = ofString "b") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_count_keybits : (ofString "count" = ofString "keybits") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_count_key : (ofString "count" = ofString "key") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_count_leaf : (ofString "count" = ofString "leaf") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_count_klen : (ofString "count" = ofString "klen") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_count_eq : (ofString "count" = ofString "eq") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_count_pos : (ofString "count" = ofString "pos") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_count_g : (ofString "count" = ofString "g") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_count_s : (ofString "count" = ofString "s") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_g_t : (ofString "g" = ofString "t") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_g_stride : (ofString "g" = ofString "stride") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_g_keys : (ofString "g" = ofString "keys") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_g_nodes : (ofString "g" = ofString "nodes") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_g_n : (ofString "g" = ofString "n") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_g_p : (ofString "g" = ofString "p") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_g_b : (ofString "g" = ofString "b") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_g_keybits : (ofString "g" = ofString "keybits") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_g_key : (ofString "g" = ofString "key") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_g_leaf : (ofString "g" = ofString "leaf") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_g_klen : (ofString "g" = ofString "klen") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_g_eq : (ofString "g" = ofString "eq") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_g_pos : (ofString "g" = ofString "pos") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_g_count : (ofString "g" = ofString "count") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_g_s : (ofString "g" = ofString "s") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_s_t : (ofString "s" = ofString "t") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_s_stride : (ofString "s" = ofString "stride") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_s_keys : (ofString "s" = ofString "keys") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_s_nodes : (ofString "s" = ofString "nodes") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_s_n : (ofString "s" = ofString "n") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_s_p : (ofString "s" = ofString "p") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_s_b : (ofString "s" = ofString "b") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_s_keybits : (ofString "s" = ofString "keybits") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_s_key : (ofString "s" = ofString "key") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_s_leaf : (ofString "s" = ofString "leaf") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_s_klen : (ofString "s" = ofString "klen") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_s_eq : (ofString "s" = ofString "eq") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_s_pos : (ofString "s" = ofString "pos") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_s_count : (ofString "s" = ofString "count") = False := by simp only [eq_iff_iff, iff_false]; decide
@[simp] theorem nm_s_g : (ofString "s" = ofString "g") = False := by simp only [eq_iff_iff, iff_false]; decide

@[simp] theorem andOp_bv (x y : BitVec 64) : AndOp.and x y = x &&& y := rfl

end InitECandidate.Solver.Wave8HtabAstra.Htab

/-! Source: Union.lean; Opus port from 3ea193df0. -/

/-! `htab_union_into_spec` from `htab_set_spec`: a flow-invariant layer (`FlowInv`) carries
`ExitR` for `dst` through the loop body (`htab_item` is read-only, `htab_set` composes by
`ExitR.trans`), and `while_inv` carries it through the loop. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace InitECandidate.Solver.Wave8HtabAstra.Htab

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8HtabAstra

def FlowR (r : Option (PanSemResultExact 64)) : Prop :=
  r = none ∨ r = some .continue ∨ r = some .break

/-- `p` never returns normally. -/
def NoRet (p : ProgHOL 64) : Prop :=
  ∀ {F : Type} (st : PanSemStateFiniteExact 64 F) v,
    (evaluateHOLFiniteState st p).1 ≠ some (.returned v)

theorem NoRet.seq {a b : ProgHOL 64} (ha : NoRet a) (hb : NoRet b) : NoRet (.seq a b) := by
  intro F st v
  rw [evaluateHOLFiniteState_seq_line780]
  rcases h : evaluateHOLFiniteState st a with ⟨r, t⟩
  have := ha st v
  rw [h] at this
  rcases r with _ | r
  · exact hb t v
  · exact this

theorem NoRet.ite {c : ExpHOL 64} {y n : ProgHOL 64} (hy : NoRet y) (hn : NoRet n) :
    NoRet (.ite c y n) := by
  intro F st v
  rw [evaluateHOLFiniteState_ite]
  split
  · split
    · exact hn st v
    · exact hy st v
  · simp

theorem NoRet.skip : NoRet .skip := by
  intro F st v; rw [evaluateHOLFiniteState_skip]; simp

theorem NoRet.assign {x : MlS} {e : ExpHOL 64} : NoRet (.assign .local x e) := by
  intro F st v
  rw [evaluateHOLFiniteState_assign]
  split
  · simp
  · split <;> simp

theorem NoRet.call0 {f : MlS} {args : List (ExpHOL 64)} :
    NoRet (.call (some (none, none)) f args) :=
  fun st v => (call0_noRetBrk st _ _).1.1 v

theorem NoRet.decCall {x f : MlS} {sh : ShapeHOL} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hc : NoRet cont) : NoRet (.decCall x sh f args cont) := by
  intro F st v
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
  split
  · simp
  · split
    · simp
    · split
      · simp
      · dsimp only
        rcases evaluateHOLFiniteState (callEntryStateHOLFinite st _) _ with ⟨r, t⟩
        rcases r with _ | r
        · simp
        · cases r with
          | returned w =>
            dsimp only
            split
            · exact hc _ v
            · simp
          | exception _ _ => simp
          | _ => simp


end InitECandidate.Solver.Wave8HtabAstra.Htab

/-! Source: FrameW.lean; Opus port from 3ea193df0. -/

/-! Local frames of local-only programs WITH loops (`htab_find_leaf`, `memeq`): every run
changes only the locals and the clock. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace InitECandidate.Solver.Wave8HtabAstra.Htab

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanRunBounded

def locOnlyW : ProgHOL 64 → Bool
  | .dec _ _ _ body => locOnlyW body
  | .seq first second => locOnlyW first && locOnlyW second
  | .ite _ yes no => locOnlyW yes && locOnlyW no
  | .while _ body => locOnlyW body
  | .assign .local _ _ => true
  | .skip | .break | .continue | .annot _ _ | .raise _ _ | .return _ => true
  | _ => false

theorem locFrameW_eval {F : Type} (p : ProgHOL 64) (hp : locOnlyW p = true)
    (s : PanSemStateFiniteExact 64 F) : LocFrame s (evaluateHOLFiniteState s p).2 := by
  cases shape : p with
  | skip => rw [evaluateHOLFiniteState_skip]; exact LocFrame.refl s
  | «break» => rw [evaluateHOLFiniteState_break]; exact LocFrame.refl s
  | «continue» => rw [evaluateHOLFiniteState_continue]; exact LocFrame.refl s
  | annot _ _ => rw [evaluateHOLFiniteState_annot]; exact LocFrame.refl s
  | raise _ _ =>
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split
      · rfl
      · exact LocFrame.refl s
    · exact LocFrame.refl s
  | «return» _ =>
    rw [evaluateHOLFiniteState_return]
    split
    · exact LocFrame.refl s
    · split
      · rfl
      · exact LocFrame.refl s
  | assign kind name e =>
    cases kind with
    | global => simp [shape, locOnlyW] at hp
    | «local» =>
      rw [evaluateHOLFiniteState_assign]
      split
      · exact LocFrame.refl s
      · split
        · rfl
        · exact LocFrame.refl s
  | dec name sh init body =>
    have hb : locOnlyW body = true := by simpa [shape, locOnlyW] using hp
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · exact LocFrame.refl s
    · rename_i val _
      split
      · have ih := locFrameW_eval body hb (setVarHOLFinite name val s)
        unfold LocFrame at ih ⊢
        dsimp only
        rw [ih]; rfl
      · exact LocFrame.refl s
  | seq first second =>
    have h12 : locOnlyW first = true ∧ locOnlyW second = true := by
      simpa [shape, locOnlyW, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_seq_line780]
    have ih1 := locFrameW_eval first h12.1 s
    have hle0 := evaluateHOLFiniteState_clock_le s first
    rcases hr1 : evaluateHOLFiniteState s first with ⟨r1, mid⟩
    rw [hr1] at ih1 hle0
    dsimp only at ih1 hle0 ⊢
    cases r1 with
    | none => exact ih1.trans (locFrameW_eval second h12.2 mid)
    | some _ => exact ih1
  | ite cond yes no =>
    have h12 : locOnlyW yes = true ∧ locOnlyW no = true := by
      simpa [shape, locOnlyW, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact locFrameW_eval no h12.2 s
      · exact locFrameW_eval yes h12.1 s
    · exact LocFrame.refl s
  | «while» cond body =>
    have hb : locOnlyW body = true := by simpa [shape, locOnlyW] using hp
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · rfl
        · dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have ih1 := locFrameW_eval body hb (decClockHOLFinite s)
          have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
          rw [hbr] at ih1 hrem
          dsimp only at ih1 hrem
          have hlt : mid.clock < s.clock := by
            change mid.clock ≤ s.clock - 1 at hrem; omega
          have h0 : LocFrame s mid := by
            unfold LocFrame at ih1 ⊢
            rw [ih1]; rfl
          cases r1 with
          | none =>
            exact h0.trans (locFrameW_eval (.while cond body) (by simpa [locOnlyW] using hb) mid)
          | some res =>
            cases res with
            | «continue» =>
              exact h0.trans (locFrameW_eval (.while cond body) (by simpa [locOnlyW] using hb) mid)
            | _ => exact h0
      · exact LocFrame.refl s
    · exact LocFrame.refl s
  | _ => simp [shape, locOnlyW] at hp
termination_by (s.clock, sizeOf p)
decreasing_by
  all_goals
    subst shape
    simp_wf
    try simp only [decClockHOLFinite, setVarHOLFinite]
    try simp only [Prod.lex_def, true_and]
    try (rw [hr1] at hle0; dsimp only at hle0)
    omega

end InitECandidate.Solver.Wave8HtabAstra.Htab

/-! Source: FindRun.lean; Opus port from 3ea193df0. -/

/-! Flow triples for one fixed state (`Flw s p Ψ`: every completed run that flows — `none`,
`continue`, `break` — satisfies `Ψ`), and the `htab_find_leaf` result invariant: under the
tree facts of `HtabWF`, the returned node is `0` or a live node, and nothing but locals changes. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.Wave8HtabAstra.Htab

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8HtabAstra

def Flw {F : Type} (s : PanSemStateFiniteExact 64 F) (p : ProgHOL 64)
    (Ψ : Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop) : Prop :=
  FlowR (evaluateHOLFiniteState s p).1 → Ψ (evaluateHOLFiniteState s p).1 (evaluateHOLFiniteState s p).2

section FlwRules
variable {F : Type} {s : PanSemStateFiniteExact 64 F}
  {Ψ : Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop}

theorem Flw.dec {x : MlS} {sh : ShapeHOL} {init : ExpHOL 64} {body : ProgHOL 64}
    (h : ∀ v, ev s init = some v →
      Flw (setVarHOLFinite x v s) body
        (fun r t => Ψ r { t with locals := HolFiniteMapExact.resVarEq t.locals (x, s.locals.lookup x) })) :
    Flw s (.dec x sh init body) Ψ := by
  intro hf
  rw [evaluateHOLFiniteState_dec_total] at hf ⊢
  dsimp only at hf ⊢
  revert hf
  split
  · intro hf; rcases hf with h | h | h <;> cases h
  · rename_i v hv
    split
    · exact h v hv
    · intro hf; rcases hf with h | h | h <;> cases h

theorem Flw.seq {a b : ProgHOL 64}
    (h : Flw s a (fun r t => (r = none → Flw t b Ψ) ∧ (r ≠ none → Ψ r t))) :
    Flw s (.seq a b) Ψ := by
  intro hf
  rw [evaluateHOLFiniteState_seq_line780] at hf ⊢
  rcases hr : evaluateHOLFiniteState s a with ⟨r, t⟩
  rw [hr] at hf
  have h' := h
  unfold Flw at h'
  rw [hr] at h'
  dsimp only at hf h' ⊢
  rcases r with _ | r
  · exact (h' (Or.inl rfl)).1 rfl hf
  · exact (h' hf).2 (by simp)

theorem Flw.ite {c : ExpHOL 64} {y n : ProgHOL 64}
    (h : ∀ w, ev s c = some (.val (.word w)) → (w ≠ 0 → Flw s y Ψ) ∧ (w = 0 → Flw s n Ψ)) :
    Flw s (.ite c y n) Ψ := by
  intro hf
  rw [evaluateHOLFiniteState_ite] at hf ⊢
  revert hf
  split
  · rename_i w hw
    split
    · rename_i hz; exact (h w hw).2 hz
    · rename_i hz; exact (h w hw).1 hz
  · intro hf; rcases hf with h | h | h <;> cases h

theorem Flw.brk (h : Ψ (some .break) s) : Flw s .break Ψ := by
  intro _; rw [evaluateHOLFiniteState_break]; exact h

theorem Flw.skip (h : Ψ none s) : Flw s .skip Ψ := by
  intro _; rw [evaluateHOLFiniteState_skip]; exact h

theorem Flw.assign {x : MlS} {e : ExpHOL 64}
    (h : ∀ v, ev s e = some v → Ψ none (setVarHOLFinite x v s)) :
    Flw s (.assign .local x e) Ψ := by
  intro hf
  rw [evaluateHOLFiniteState_assign] at hf ⊢
  revert hf
  split
  · intro hf; rcases hf with h | h | h <;> cases h
  · rename_i v hv
    split
    · intro _; exact h v hv
    · intro hf; rcases hf with h | h | h <;> cases h

end FlwRules

theorem ofNat_node_addr (nd w : BitVec 64) (off : Nat) :
    BitVec.ofNat 64 (nd.toNat + 32 * w.toNat + off) = nd + w * 32 + BitVec.ofNat 64 off := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  have : (32 : BitVec 64).toNat = 32 := rfl
  rw [this]
  omega

theorem memW_node {F : Type} (x : PanSemStateFiniteExact 64 F) (nd w : BitVec 64) (off : Nat) :
    memW x (nd.toNat + 32 * w.toNat + off) =
      (match x.memory (nd + w * 32 + BitVec.ofNat 64 off) with | .word u => u.toNat) := by
  unfold memW; rw [ofNat_node_addr]

theorem ev_node_load {F : Type} (s : PanSemStateFiniteExact 64 F) (nd w off : BitVec 64)
    (h1 : s.locals.lookup (ofString "nodes") = some (.val (.word nd)))
    (h2 : s.locals.lookup (ofString "n") = some (.val (.word w))) (v : ValueHOL 64)
    (h : ev s (.load .one (.op .add [.var .local (ofString "nodes"),
      .panop .mul [.var .local (ofString "n"), .const 32], .const off])) = some v) :
    s.memaddrs (nd + w * 32 + off) ∧ v = .val (s.memory (nd + w * 32 + off)) := by
  simp [ev, evalHOLExact, evalListHOLExact, h1, h2, panOpHOL, valueIsWord, valueWord, wordOpHOL,
    wordOp, memLoadHOLExact] at h
  rw [BitVec.add_assoc]
  exact ⟨h.1, h.2.symm⟩

/-- One iteration of the `htab_find_leaf` descent: the next `n` is again `0` or live. -/
theorem fl_iter {F : Type} (x : PanSemStateFiniteExact 64 F) (nd w kb : BitVec 64)
    (S : List Nat)
    (hnd : x.locals.lookup (ofString "nodes") = some (.val (.word nd)))
    (hn : x.locals.lookup (ofString "n") = some (.val (.word w)))
    (hkb : x.locals.lookup (ofString "keybits") = some (.val (.word kb)))
    (hw : w.toNat ∈ S)
    (htree : memW x (nd.toNat + 32 * w.toNat + 24) ≠ kb.toNat →
      memW x (nd.toNat + 32 * w.toNat + 8) ∈ S ∧ memW x (nd.toNat + 32 * w.toNat + 16) ∈ S)
    (body : ProgHOL 64)
    (hbody : body = .dec (ofString "b") .one (.load .one (.op .add [.var .local (ofString "nodes"),
        .panop .mul [.var .local (ofString "n"), .const 32], .const 24]))
      (.seq (.ite (.cmp .equal (.var .local (ofString "b")) (.var .local (ofString "keybits")))
          .break .skip)
        (.ite (.cmp .equal (.op .and [.shift .lsr (.loadByte (.op .add [.var .local (ofString "key"),
            .shift .lsr (.var .local (ofString "b")) (.const 3)])) (.op .sub [.const 7,
            .op .and [.var .local (ofString "b"), .const 7]]), .const 1]) (.const 0))
          (.assign .local (ofString "n") (.load .one (.op .add [.var .local (ofString "nodes"),
            .panop .mul [.var .local (ofString "n"), .const 32], .const 8])))
          (.assign .local (ofString "n") (.load .one (.op .add [.var .local (ofString "nodes"),
            .panop .mul [.var .local (ofString "n"), .const 32], .const 16]))))))
    : Flw x body (fun _ t => ∃ w' : BitVec 64,
        t.locals.lookup (ofString "n") = some (.val (.word w')) ∧ w'.toNat ∈ S) := by
  subst hbody
  apply Flw.dec
  intro bv hbv
  obtain ⟨_, rfl⟩ := ev_node_load x nd w 24 hnd hn bv hbv
  apply Flw.seq
  apply Flw.ite
  intro c hc
  constructor
  · intro _
    apply Flw.brk
    refine ⟨fun h => absurd h (by simp), fun _ => ?_⟩
    refine ⟨w, ?_, hw⟩
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, PanRunBounded.resVarEq_lookup,
      hn]
  · intro hz
    apply Flw.skip
    refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
    have hne : memW x (nd.toNat + 32 * w.toNat + 24) ≠ kb.toNat := by
      obtain ⟨a, b, ha, hb, hcw⟩ := evalAt_cmp _ .equal _ _ c hc
      simp [evalAt, evalHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE] at ha
      simp [evalAt, evalHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        hkb] at hb
      subst hb
      rw [memW_node]
      have ha' : x.memory (nd + w * 32 + BitVec.ofNat 64 24) = .word a := ha
      rw [ha']
      intro heq
      have := BitVec.eq_of_toNat_eq heq
      subst this hz
      simp [Compiler.Encoders.Asm.wordCmpHOL] at hcw
    obtain ⟨h8, h16⟩ := htree hne
    apply Flw.ite
    intro c2 _
    constructor
    · intro _
      apply Flw.assign
      intro v hv
      obtain ⟨_, rfl⟩ := ev_node_load _ nd w 8
        (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hnd])
        (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn]) v hv
      rw [memW_node] at h8
      rcases hm : x.memory (nd + w * 32 + 8) with ⟨u⟩
      refine ⟨u, ?_, ?_⟩
      · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          PanRunBounded.resVarEq_lookup]
        exact hm
      · have : x.memory (nd + w * 32 + BitVec.ofNat 64 8) = .word u := hm
        rw [this] at h8; exact h8
    · intro _
      apply Flw.assign
      intro v hv
      obtain ⟨_, rfl⟩ := ev_node_load _ nd w 16
        (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hnd])
        (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn]) v hv
      rw [memW_node] at h16
      rcases hm : x.memory (nd + w * 32 + 16) with ⟨u⟩
      refine ⟨u, ?_, ?_⟩
      · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          PanRunBounded.resVarEq_lookup]
        exact hm
      · have : x.memory (nd + w * 32 + BitVec.ofNat 64 16) = .word u := hm
        rw [this] at h16; exact h16

theorem ev_field_load {F : Type} (s : PanSemStateFiniteExact 64 F) (x : MlS) (tw off : BitVec 64)
    (h1 : s.locals.lookup x = some (.val (.word tw))) (v : ValueHOL 64)
    (h : ev s (.load .one (.op .add [.var .local x, .const off])) = some v) :
    s.memaddrs (tw + off) ∧ v = .val (s.memory (tw + off)) := by
  simp [ev, evalHOLExact, evalListHOLExact, h1, valueIsWord, valueWord, wordOpHOL,
    wordOp, memLoadHOLExact] at h
  exact ⟨h.1, h.2.symm⟩

theorem NoRet.dec' {x : MlS} {sh : ShapeHOL} {e : ExpHOL 64} {p : ProgHOL 64} (hp : NoRet p) :
    NoRet (.dec x sh e p) := by
  intro F st v
  rcases dec_res st x sh e p with h | ⟨w, h⟩
  · rw [h]; simp
  · rw [h]; exact hp _ v

theorem NoRet.brk : NoRet .break := by
  intro F st v; rw [evaluateHOLFiniteState_break]; simp

theorem LocFrame.locals {F : Type} {s t : PanSemStateFiniteExact 64 F} (h : LocFrame s t)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) : LocFrame s { t with locals := L } := by
  unfold LocFrame at *
  rw [h]

theorem LocFrame.setVar {F : Type} {s t : PanSemStateFiniteExact 64 F} (h : LocFrame s t)
    (x : MlS) (v : ValueHOL 64) : LocFrame s (setVarHOLFinite x v t) := h.locals _

theorem LocFrame.emptyLocals {F : Type} {s t : PanSemStateFiniteExact 64 F} (h : LocFrame s t) :
    LocFrame s (emptyLocalsHOLFinite t) := h.locals _

theorem LocFrame.memory {F : Type} {s t : PanSemStateFiniteExact 64 F} (h : LocFrame s t) :
    t.memory = s.memory := by
  unfold LocFrame at h; rw [h]

theorem locFrame_dec {F : Type} {s : PanSemStateFiniteExact 64 F} (p : ProgHOL 64)
    (hp : locOnly p = true) : LocFrame s (evaluateHOLFiniteState (decClockHOLFinite s) p).2 := by
  have := locFrame_eval p hp (decClockHOLFinite s)
  unfold LocFrame at this ⊢
  rw [this]; rfl

theorem flowing_of_flowR {r : Option (PanSemResultExact 64)} (h : FlowR r) : Flowing r := by
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)

theorem active_n_ne {F : Type} (x : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hn : x.locals.lookup (ofString "n") = some (.val (.word w)))
    (h : LoopActive (.cmp .notEqual (.var .local (ofString "n")) (.const 0)) x) : w ≠ 0 := by
  obtain ⟨c, hc, hnz⟩ := h
  change evalAt x _ = _ at hc
  obtain ⟨a, b, ha, hb, hcw⟩ := evalAt_cmp x .notEqual _ _ c hc
  simp [evalAt, evalHOLExact, hn] at ha
  simp [evalAt, evalHOLExact] at hb
  subst ha hb
  intro hw; subst hw
  simp [Compiler.Encoders.Asm.wordCmpHOL] at hcw
  exact hnz hcw

/-- `htab_find_leaf` returns `0` or a node of `S` (when `S` is closed under the descent), and
changes nothing but locals and clock. -/
theorem find_leaf_ret {F : Type} (E : PanSemStateFiniteExact 64 F)
    (tw : BitVec 64) (ht : E.locals.lookup (ofString "t") = some (.val (.word tw)))
    (S : List Nat)
    (hroot : ∀ u, E.memory (tw + 56) = .word u → u.toNat ∈ S)
    (htree : ∀ nd k : BitVec 64, E.memory (tw + 40) = .word nd → E.memory (tw + 0) = .word k →
      ∀ w : BitVec 64, w.toNat ∈ S → w ≠ 0 →
        memW E (nd.toNat + 32 * w.toNat + 24) ≠ (k * 8).toNat →
        memW E (nd.toNat + 32 * w.toNat + 8) ∈ S ∧ memW E (nd.toNat + 32 * w.toNat + 16) ∈ S) :
    Ret E (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
      (extractFn Guest.Software.guestFn_htab_find_leaf).body)
      (fun v post => ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat ∈ S ∧ LocFrame E post) := by
  htab_unfold Guest.Software.guestFn_htab_find_leaf
  apply Ret.dec
  intro kbv hkbv
  rcases hk : E.memory (tw + 0) with ⟨k⟩
  have hk' : E.memory tw = .word k := by simpa using hk
  have hkbv' : kbv = .val (.word (k * 8)) := by
    simp [ev, evalHOLExact, evalListHOLExact, ht, valueIsWord, valueWord, wordOpHOL, wordOp,
      memLoadHOLExact, panOpHOL, hk'] at hkbv
    by_cases hm : E.memaddrs tw
    · simp [hm] at hkbv; exact hkbv.symm
    · simp [hm] at hkbv
  subst hkbv'
  apply Ret.dec
  intro ndv hndv
  rcases hnd : E.memory (tw + 40) with ⟨nd⟩
  obtain ⟨_, rfl⟩ := ev_field_load _ (ofString "t") tw 40
    (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht]) ndv hndv
  apply Ret.dec
  intro nv hnv
  rcases hrt : E.memory (tw + 56) with ⟨r0⟩
  obtain ⟨_, rfl⟩ := ev_field_load _ (ofString "t") tw 56
    (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht]) nv hnv
  simp only [setVarHOLFinite] at *
  set E3 := { E with locals := ((E.locals.update (ofString "keybits", .val (.word (k * 8)))).update
    (ofString "nodes", .val (E.memory (tw + 40)))).update (ofString "n", .val (E.memory (tw + 56))) }
    with hE3
  apply Ret.seq
  · intro w hw
    exfalso
    revert hw
    apply while_noRet _ _ _ _ _ le_rfl
    exact NoRet.dec' (NoRet.seq (NoRet.ite NoRet.brk NoRet.skip) (NoRet.ite NoRet.assign NoRet.assign))
  · intro u hu
    let J : PanSemStateFiniteExact 64 F → Prop := fun y =>
      LocFrame E y ∧ y.locals.lookup (ofString "nodes") = some (.val (.word nd)) ∧
        y.locals.lookup (ofString "keybits") = some (.val (.word (k * 8))) ∧
        ∃ w : BitVec 64, y.locals.lookup (ofString "n") = some (.val (.word w)) ∧ w.toNat ∈ S
    have hJ3 : J E3 := by
      refine ⟨LocFrame.locals (LocFrame.refl E) _, ?_, ?_, r0, ?_, hroot r0 hrt⟩
      · simp [hE3, HolFiniteMapExact.lookup_update, FUPDATE]; exact hnd
      · simp [hE3, HolFiniteMapExact.lookup_update, FUPDATE]
      · simp [hE3, HolFiniteMapExact.lookup_update, FUPDATE]; exact hrt
    have hJu : J u := by
      have := while_inv_act J _ _ ?_ E3.clock E3 le_rfl hJ3 (by rw [hu])
      · rw [hu] at this; exact this
      · intro x hx hact _ hflow
        obtain ⟨hfr, hxnd, hxkb, w, hxn, hwS⟩ := hx
        have hw0 := active_n_ne x w hxn hact
        have hmem := hfr.memory
        have hit := fl_iter (decClockHOLFinite x) nd w (k * 8) S hxnd hxn hxkb hwS (by
          intro hne
          have hm : ∀ a, memW (decClockHOLFinite x) a = memW E a := fun a => by
            simp only [memW, decClockHOLFinite, hmem]
          simp only [hm] at hne ⊢
          exact htree nd k hnd hk w hwS hw0 hne) _ rfl hflow
        obtain ⟨w', hw', hw'S⟩ := hit
        refine ⟨?_, ?_, ?_, w', hw', hw'S⟩
        · exact hfr.trans (locFrame_dec _ (by rfl))
        · rw [evaluate_avoidsLocal_flowing _ _ (by simp [avoidsLocal]) _ (flowing_of_flowR hflow)]
          exact hxnd
        · rw [evaluate_avoidsLocal_flowing _ _ (by simp [avoidsLocal]) _ (flowing_of_flowR hflow)]
          exact hxkb
    apply Ret.ret
    intro val hval
    obtain ⟨hfr, _, _, w, hun, hwS⟩ := hJu
    simp [ev, evalHOLExact, hun] at hval
    subst hval
    exact ⟨w, rfl, hwS, (hfr.emptyLocals.locals _).locals _ |>.locals _ |>.locals _⟩


theorem Flw.and {F : Type} {s : PanSemStateFiniteExact 64 F} {p : ProgHOL 64}
    {Ψ1 Ψ2 : Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop}
    (h1 : Flw s p Ψ1) (h2 : Flw s p Ψ2) : Flw s p (fun r t => Ψ1 r t ∧ Ψ2 r t) :=
  fun hf => ⟨h1 hf, h2 hf⟩

/-- A breaking iteration of the descent stops at a node whose crit bit is `keybits`. -/
theorem fl_brk {F : Type} (x : PanSemStateFiniteExact 64 F) (nd w kb : BitVec 64)
    (hnd : x.locals.lookup (ofString "nodes") = some (.val (.word nd)))
    (hn : x.locals.lookup (ofString "n") = some (.val (.word w)))
    (hkb : x.locals.lookup (ofString "keybits") = some (.val (.word kb)))
    (body : ProgHOL 64)
    (hbody : body = .dec (ofString "b") .one (.load .one (.op .add [.var .local (ofString "nodes"),
        .panop .mul [.var .local (ofString "n"), .const 32], .const 24]))
      (.seq (.ite (.cmp .equal (.var .local (ofString "b")) (.var .local (ofString "keybits")))
          .break .skip)
        (.ite (.cmp .equal (.op .and [.shift .lsr (.loadByte (.op .add [.var .local (ofString "key"),
            .shift .lsr (.var .local (ofString "b")) (.const 3)])) (.op .sub [.const 7,
            .op .and [.var .local (ofString "b"), .const 7]]), .const 1]) (.const 0))
          (.assign .local (ofString "n") (.load .one (.op .add [.var .local (ofString "nodes"),
            .panop .mul [.var .local (ofString "n"), .const 32], .const 8])))
          (.assign .local (ofString "n") (.load .one (.op .add [.var .local (ofString "nodes"),
            .panop .mul [.var .local (ofString "n"), .const 32], .const 16]))))))
    : Flw x body (fun r t => r = some .break →
        t.locals.lookup (ofString "n") = some (.val (.word w)) ∧
        memW x (nd.toNat + 32 * w.toNat + 24) = kb.toNat) := by
  subst hbody
  apply Flw.dec
  intro bv hbv
  obtain ⟨_, rfl⟩ := ev_node_load x nd w 24 hnd hn bv hbv
  apply Flw.seq
  apply Flw.ite
  intro c hc
  constructor
  · intro hc0
    apply Flw.brk
    refine ⟨fun h => absurd h (by simp), fun _ _ => ⟨?_, ?_⟩⟩
    · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        PanRunBounded.resVarEq_lookup, hn]
    · obtain ⟨a, b, ha, hb, hcw⟩ := evalAt_cmp _ .equal _ _ c hc
      simp [evalAt, evalHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE] at ha
      simp [evalAt, evalHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        hkb] at hb
      subst hb
      have hab : a = kb := by
        by_contra hne
        simp [Compiler.Encoders.Asm.wordCmpHOL, hne] at hcw
        exact hc0 hcw
      subst hab
      rw [memW_node]
      have ha' : x.memory (nd + w * 32 + BitVec.ofNat 64 24) = .word a := ha
      rw [ha']
  · intro _
    apply Flw.skip
    refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
    apply Flw.ite
    intro c2 _
    constructor <;> intro _ <;> apply Flw.assign <;> intro v _ <;> intro h <;> cases h

/-- `htab_find_leaf` returns `0` or a node of `S` (when `S` is closed under the descent), and
changes nothing but locals and clock. -/
theorem find_leaf_ret2 {F : Type} (E : PanSemStateFiniteExact 64 F)
    (tw : BitVec 64) (ht : E.locals.lookup (ofString "t") = some (.val (.word tw)))
    (S : List Nat)
    (hroot : ∀ u, E.memory (tw + 56) = .word u → u.toNat ∈ S)
    (htree : ∀ nd k : BitVec 64, E.memory (tw + 40) = .word nd → E.memory (tw + 0) = .word k →
      ∀ w : BitVec 64, w.toNat ∈ S → w ≠ 0 →
        memW E (nd.toNat + 32 * w.toNat + 24) ≠ (k * 8).toNat →
        memW E (nd.toNat + 32 * w.toNat + 8) ∈ S ∧ memW E (nd.toNat + 32 * w.toNat + 16) ∈ S) :
    Ret E (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
      (extractFn Guest.Software.guestFn_htab_find_leaf).body)
      (fun v post => ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat ∈ S ∧ LocFrame E post ∧
        (w ≠ 0 → ∀ nd k : BitVec 64, E.memory (tw + 40) = .word nd → E.memory (tw + 0) = .word k →
          memW E (nd.toNat + 32 * w.toNat + 24) = (k * 8).toNat)) := by
  htab_unfold Guest.Software.guestFn_htab_find_leaf
  apply Ret.dec
  intro kbv hkbv
  rcases hk : E.memory (tw + 0) with ⟨k⟩
  have hk' : E.memory tw = .word k := by simpa using hk
  have hkbv' : kbv = .val (.word (k * 8)) := by
    simp [ev, evalHOLExact, evalListHOLExact, ht, valueIsWord, valueWord, wordOpHOL, wordOp,
      memLoadHOLExact, panOpHOL, hk'] at hkbv
    by_cases hm : E.memaddrs tw
    · simp [hm] at hkbv; exact hkbv.symm
    · simp [hm] at hkbv
  subst hkbv'
  apply Ret.dec
  intro ndv hndv
  rcases hnd : E.memory (tw + 40) with ⟨nd⟩
  obtain ⟨_, rfl⟩ := ev_field_load _ (ofString "t") tw 40
    (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht]) ndv hndv
  apply Ret.dec
  intro nv hnv
  rcases hrt : E.memory (tw + 56) with ⟨r0⟩
  obtain ⟨_, rfl⟩ := ev_field_load _ (ofString "t") tw 56
    (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht]) nv hnv
  simp only [setVarHOLFinite] at *
  set E3 := { E with locals := ((E.locals.update (ofString "keybits", .val (.word (k * 8)))).update
    (ofString "nodes", .val (E.memory (tw + 40)))).update (ofString "n", .val (E.memory (tw + 56))) }
    with hE3
  apply Ret.seq
  · intro w hw
    exfalso
    revert hw
    apply while_noRet _ _ _ _ _ le_rfl
    exact NoRet.dec' (NoRet.seq (NoRet.ite NoRet.brk NoRet.skip) (NoRet.ite NoRet.assign NoRet.assign))
  · intro u hu
    let J : PanSemStateFiniteExact 64 F → Prop := fun y =>
      LocFrame E y ∧ y.locals.lookup (ofString "nodes") = some (.val (.word nd)) ∧
        y.locals.lookup (ofString "keybits") = some (.val (.word (k * 8))) ∧
        ∃ w : BitVec 64, y.locals.lookup (ofString "n") = some (.val (.word w)) ∧ w.toNat ∈ S
    have hJ3 : J E3 := by
      refine ⟨LocFrame.locals (LocFrame.refl E) _, ?_, ?_, r0, ?_, hroot r0 hrt⟩
      · simp [hE3, HolFiniteMapExact.lookup_update, FUPDATE]; exact hnd
      · simp [hE3, HolFiniteMapExact.lookup_update, FUPDATE]
      · simp [hE3, HolFiniteMapExact.lookup_update, FUPDATE]; exact hrt
    let Bk : PanSemStateFiniteExact 64 F → Prop := fun y => J y ∧
      ∃ w : BitVec 64, y.locals.lookup (ofString "n") = some (.val (.word w)) ∧
        memW E (nd.toNat + 32 * w.toNat + 24) = (k * 8).toNat
    have hJu : (J u ∧ CondFalse (.cmp .notEqual (.var .local (ofString "n")) (.const 0)) u) ∨ Bk u := by
      have := while_inv2 J Bk _ _ ?_ E3.clock E3 le_rfl hJ3 (by rw [hu])
      · rw [hu] at this; exact this
      · intro x hx hact _
        obtain ⟨hfr, hxnd, hxkb, w, hxn, hwS⟩ := hx
        have hw0 := active_n_ne x w hxn hact
        have hmem := hfr.memory
        have hm : ∀ a, memW (decClockHOLFinite x) a = memW E a := fun a => by
          simp only [memW, decClockHOLFinite, hmem]
        constructor
        · intro hflow
          have hflow' : FlowR _ := hflow.elim Or.inl (fun h => Or.inr (Or.inl h))
          have hit := fl_iter (decClockHOLFinite x) nd w (k * 8) S hxnd hxn hxkb hwS (by
            intro hne
            simp only [hm] at hne ⊢
            exact htree nd k hnd hk w hwS hw0 hne) _ rfl hflow'
          obtain ⟨w', hw', hw'S⟩ := hit
          refine ⟨hfr.trans (locFrame_dec _ (by rfl)), ?_, ?_, w', hw', hw'S⟩
          · rw [evaluate_avoidsLocal_flowing _ _ (by simp [avoidsLocal]) _ (flowing_of_flowR hflow')]
            exact hxnd
          · rw [evaluate_avoidsLocal_flowing _ _ (by simp [avoidsLocal]) _ (flowing_of_flowR hflow')]
            exact hxkb
        · intro hbrk
          have hflow' : FlowR _ := Or.inr (Or.inr hbrk)
          have hbk := fl_brk (decClockHOLFinite x) nd w (k * 8) hxnd hxn hxkb _ rfl hflow' hbrk
          obtain ⟨hn', hcrit⟩ := hbk
          refine ⟨⟨hfr.trans (locFrame_dec _ (by rfl)), ?_, ?_, w, hn', hwS⟩, w, hn', ?_⟩
          · rw [evaluate_avoidsLocal_flowing _ _ (by simp [avoidsLocal]) _ (flowing_of_flowR hflow')]
            exact hxnd
          · rw [evaluate_avoidsLocal_flowing _ _ (by simp [avoidsLocal]) _ (flowing_of_flowR hflow')]
            exact hxkb
          · rw [hm] at hcrit
            exact hcrit
    apply Ret.ret
    intro val hval
    rcases hJu with ⟨⟨hfr, _, _, w, hun, hwS⟩, hcf⟩ | ⟨⟨hfr, _, _, w0, hun0, hwS0⟩, w, hun, hcrit⟩
    · simp [ev, evalHOLExact, hun] at hval
      subst hval
      refine ⟨w, rfl, hwS, (hfr.emptyLocals.locals _).locals _ |>.locals _ |>.locals _, ?_⟩
      intro hw0
      exfalso
      unfold CondFalse at hcf
      change evalAt u _ = _ at hcf
      obtain ⟨a, b, ha, hb, hcw⟩ := evalAt_cmp u .notEqual _ _ 0 hcf
      simp [evalAt, evalHOLExact, hun] at ha hb
      subst ha hb
      simp [Compiler.Encoders.Asm.wordCmpHOL, hw0] at hcw
      exact hw0 hcw
    · simp [ev, evalHOLExact, hun] at hval
      subst hval
      refine ⟨w, rfl, ?_, (hfr.emptyLocals.locals _).locals _ |>.locals _ |>.locals _, ?_⟩
      · rw [hun0] at hun
        simp at hun
        rw [← hun]; exact hwS0
      · intro _ nd' k' hnd' hk'
        simp only [HolWordLab.word.injEq] at hnd' hk'
        subst hnd' hk'
        exact hcrit


end InitECandidate.Solver.Wave8HtabAstra.Htab

/-! Source: DelTools.lean; Opus port from 3ea193df0. -/

/-! Tools for `htab_del_progress_spec`: a generic `decCall` rule for `Ret`, a store rule for
`Flw`, and word-address arithmetic inside the table blocks. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.Wave8HtabAstra.Htab

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8HtabAstra

/-- `decCall` for `Ret`: the continuation starts from the resumed state after a normal return. -/
theorem Ret.decCall_gen {F : Type} {s : PanSemStateFiniteExact 64 F} {x fname : MlS}
    {sh : ShapeHOL} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hk : ∀ values body callee ret v post,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values →
      lookupCodeHOLFinite s.code.lookup fname values = some (body, callee, ret) →
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post) →
      Ret (setVarHOLFinite x v { post with locals := s.locals }) cont
        (fun w t => Φ w { t with locals := HolFiniteMapExact.resVarEq t.locals (x, s.locals.lookup x) })) :
    Ret s (.decCall x sh fname args cont) Φ := by
  intro v hv
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hv ⊢
  revert hv
  split
  · simp
  · rename_i values hargs
    split
    · simp
    · rename_i body callee ret hl
      split
      · simp
      · dsimp only
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨r, post⟩
        dsimp only
        rcases r with _ | r
        · simp
        · cases r with
          | returned w =>
            dsimp only
            split
            · intro hv
              exact hk values body callee ret w post hargs hl hrun v hv
            · simp
          | exception _ _ => simp
          | _ => simp

theorem Flw.storeW {F : Type} {s : PanSemStateFiniteExact 64 F} {d e : ExpHOL 64}
    {Ψ : Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop}
    (a w : BitVec 64) (hd : ev s d = some (.val (.word a))) (he : ev s e = some (.val (.word w)))
    (h : s.memaddrs a → Ψ none { s with memory := updW s.memory a w }) :
    Flw s (.store d e) Ψ := by
  intro hf
  rw [evaluateHOLFiniteState_store] at hf ⊢
  simp only [ev] at hd he
  rw [hd] at hf ⊢
  dsimp only at hf ⊢
  rw [he] at hf ⊢
  dsimp only at hf ⊢
  revert hf
  split
  · rename_i m hm
    intro _
    obtain ⟨hdom, rfl⟩ := stores_word _ hm
    exact h hdom
  · intro hf; rcases hf with h | h | h <;> cases h

end InitECandidate.Solver.Wave8HtabAstra.Htab

namespace InitECandidate.Solver.Wave8HtabAstra.Htab
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanRunBounded

theorem ev_idx_load {F : Type} (s : PanSemStateFiniteExact 64 F) (bx ix : MlS) (b i sc off : BitVec 64)
    (h1 : s.locals.lookup bx = some (.val (.word b)))
    (h2 : s.locals.lookup ix = some (.val (.word i))) (v : ValueHOL 64)
    (h : ev s (.load .one (.op .add [.var .local bx,
      .panop .mul [.var .local ix, .const sc], .const off])) = some v) :
    s.memaddrs (b + i * sc + off) ∧ v = .val (s.memory (b + i * sc + off)) := by
  simp [ev, evalHOLExact, evalListHOLExact, h1, h2, panOpHOL, valueIsWord, valueWord, wordOpHOL,
    wordOp, memLoadHOLExact] at h
  rw [BitVec.add_assoc]
  exact ⟨h.1, h.2.symm⟩

theorem ev_idx2_load {F : Type} (s : PanSemStateFiniteExact 64 F) (bx ix : MlS) (b i sc : BitVec 64)
    (h1 : s.locals.lookup bx = some (.val (.word b)))
    (h2 : s.locals.lookup ix = some (.val (.word i))) (v : ValueHOL 64)
    (h : ev s (.load .one (.op .add [.var .local bx,
      .panop .mul [.var .local ix, .const sc]])) = some v) :
    s.memaddrs (b + i * sc) ∧ v = .val (s.memory (b + i * sc)) := by
  simp [ev, evalHOLExact, evalListHOLExact, h1, h2, panOpHOL, valueIsWord, valueWord, wordOpHOL,
    wordOp, memLoadHOLExact] at h
  exact ⟨h.1, h.2.symm⟩

theorem ev_idx_addr {F : Type} (s : PanSemStateFiniteExact 64 F) (bx ix : MlS) (b i sc off : BitVec 64)
    (h1 : s.locals.lookup bx = some (.val (.word b)))
    (h2 : s.locals.lookup ix = some (.val (.word i))) :
    ev s (.op .add [.var .local bx, .panop .mul [.var .local ix, .const sc], .const off]) =
      some (.val (.word (b + i * sc + off))) := by
  simp [ev, evalHOLExact, evalListHOLExact, h1, h2, panOpHOL, valueIsWord, valueWord, wordOpHOL,
    wordOp]
  rw [BitVec.add_assoc]

theorem ev_idx2_addr {F : Type} (s : PanSemStateFiniteExact 64 F) (bx ix : MlS) (b i sc : BitVec 64)
    (h1 : s.locals.lookup bx = some (.val (.word b)))
    (h2 : s.locals.lookup ix = some (.val (.word i))) :
    ev s (.op .add [.var .local bx, .panop .mul [.var .local ix, .const sc]]) =
      some (.val (.word (b + i * sc))) := by
  simp [ev, evalHOLExact, evalListHOLExact, h1, h2, panOpHOL, valueIsWord, valueWord, wordOpHOL,
    wordOp]

theorem ev_fld_addr {F : Type} (s : PanSemStateFiniteExact 64 F) (bx : MlS) (b off : BitVec 64)
    (h1 : s.locals.lookup bx = some (.val (.word b))) :
    ev s (.op .add [.var .local bx, .const off]) = some (.val (.word (b + off))) := by
  simp [ev, evalHOLExact, evalListHOLExact, h1, valueIsWord, valueWord, wordOpHOL, wordOp]

theorem ev_var {F : Type} (s : PanSemStateFiniteExact 64 F) (x : MlS) (v : ValueHOL 64)
    (h1 : s.locals.lookup x = some v) : ev s (.var .local x) = some v := by
  simp [ev, evalHOLExact, h1]

theorem updW_ne (m : BitVec 64 → HolWordLab 64) (a w b : BitVec 64) (h : b ≠ a) :
    updW m a w b = m b := by simp [updW, h]

theorem updW_eq (m : BitVec 64 → HolWordLab 64) (a w : BitVec 64) : updW m a w a = .word w := by
  simp [updW]

/-- Distinct word addresses by their numeric values (no wrap-around). -/
theorem addr_ne {a b : BitVec 64} (h : a.toNat ≠ b.toNat) : a ≠ b := fun e => h (by rw [e])

theorem idx_toNat (b i : BitVec 64) (sc off : Nat) (hsc : sc < 2 ^ 64) (hoff : off < 2 ^ 64)
    (h : b.toNat + i.toNat * sc + off < 2 ^ 64) :
    (b + i * BitVec.ofNat 64 sc + BitVec.ofNat 64 off).toNat = b.toNat + i.toNat * sc + off := by
  have hi : i.toNat * sc < 2 ^ 64 := by omega
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsc,
    Nat.mod_eq_of_lt hoff, Nat.mod_eq_of_lt hi]
  omega

end InitECandidate.Solver.Wave8HtabAstra.Htab

namespace InitECandidate.Solver.Wave8HtabAstra.Htab
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem ev_field_sub1 {F : Type} (s : PanSemStateFiniteExact 64 F) (x : MlS) (tw off u : BitVec 64)
    (h1 : s.locals.lookup x = some (.val (.word tw))) (hm : s.memory (tw + off) = .word u)
    (v : ValueHOL 64)
    (h : ev s (.op .sub [.load .one (.op .add [.var .local x, .const off]), .const 1]) = some v) :
    v = .val (.word (u - 1)) := by
  simp [ev, evalHOLExact, evalListHOLExact, h1, valueIsWord, valueWord, wordOpHOL,
    wordOp, memLoadHOLExact, hm] at h
  by_cases hd : s.memaddrs (tw + off)
  · simp [hd] at h; rw [← h]; rfl
  · simp [hd] at h

end InitECandidate.Solver.Wave8HtabAstra.Htab
