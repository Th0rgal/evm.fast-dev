
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
mark taken by the same activation (the contract of every caller, §7). -/
def ArenaOK {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  sourceBase ≤ globN s "heap_ptr" ∧ globN s "heap_ptr" ≤ heapLimit ∧
  scratchStart ≤ globN s "frame_mem_ptr" ∧ globN s "frame_mem_ptr" ≤ globN s "scratch_ptr" ∧
  globN s "scratch_ptr" ≤ scratchEnd

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

/-- Memory outside `keep ∪ fresh` is unchanged from `s` to `post`. Addresses are the 64-bit
words themselves, tested through `toNat` (round-2 Astra item 1: quantifying over `a : Nat` and
reading `BitVec.ofNat 64 a` made `x + 2^64` an outside alias of every changed `x`). -/
def FrameOutside {F : Type} (s post : PanSemStateFiniteExact 64 F) (keep : List Ivl)
    (fresh : Ivl) : Prop :=
  ∀ a : BitVec 64, (∀ i ∈ keep, ¬ InIvl a.toNat i) → ¬ InIvl a.toNat fresh →
    post.memory a = s.memory a

/-- Regression (round-2 Astra item 1): a single store inside `fresh` respects the frame. -/
example {F : Type} (s : PanSemStateFiniteExact 64 F) (x : BitVec 64) (w : HolWordLab 64) :
    FrameOutside s { s with memory := fun b => if b = x then w else s.memory b } [] (x.toNat, 8) := by
  intro a _ hout
  have hne : a ≠ x := by
    rintro rfl
    exact hout ⟨Nat.le_refl _, by omega⟩
  simp [hne]

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

/-- `htab_union_into(dst, src)`: the same contract for `dst` (whatever `src` is, even `src = dst`
or a table aliasing `dst`'s header: round-1 item 3). -/
def UnionArgWF : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ HtabWF s (locN s "dst") ∧
    ∀ i ∈ htabFootprint s (locN s "dst"), Allocated s i

def UnionExit : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Prop :=
  fun s post =>
    let t := locN s "dst"
    let fresh : Ivl := (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr")
    ArenaReady post ∧ HtabWF post t ∧
    globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
    (∀ i ∈ htabFootprint post t, Allocated post i) ∧
    FrameOutside s post (htabFootprint s t) fresh ∧
    (∀ name, name ≠ "heap_ptr" → s.globals.lookup (ofString name) = post.globals.lookup (ofString name))

/-! ### Global state typing: `WorldOK`

Roots (read off `state_init` 12716-12774, `state_fresh_tx` 12778, `bal_init` 13871): the record
`ws` (40 B; table at `+32`), `bs` (80 B; tables at `+8..+48`, `+72`), `ts` (72 B; tables at
`+8..+64`), the globals `bal_accounts`, `bal_idx_accts`, `bal_idx_stor`, and the journal. A root
slot holding `0` is allowed (every access through it errors: `0 + off ∉ ordinaryDomain`); before
`state_init` all of them are `0`, so `WorldOK` holds right after `mem_init`. `bs+32` and `ts+32`
are tables of tables (`set_storage` 13456, `merge_tx_into_block` 13748): their live values are
tables again. Values of every other table are never written through (accounts are updated
copy-on-write: `set_account_balance`, `increment_nonce`), so they are unconstrained. -/

/-- Record slots holding table pointers. -/
def wsTableSlots : List Nat := [32]
def bsTableSlots : List Nat := [8, 16, 24, 32, 40, 48, 72]
def tsTableSlots : List Nat := [8, 16, 24, 32, 40, 48, 56, 64]
def globalTableRoots : List String := ["bal_accounts", "bal_idx_accts", "bal_idx_stor"]

/-- Every global that holds a buffer allocated with a literal size (`alloc(n)` assigned to the
global in the `*_init` functions, `state_init`, `state_fresh_tx`, `bal_init`; generated by
`coverage.py`, `out/tiers.txt`), including the records `ws` (40 B), `bs` (80 B), `ts` (72 B). -/
def globalBuffers : List (String × Nat) :=
  [("b2_iv", 64), ("b2_sigma", 80), ("b2_v", 128), ("bal_key_buf", 64), ("be", 120), ("beacon_roots_address", 24), ("bls_c", 7136), ("bo", 88), ("bs", 80), ("builder_deposit_address", 24), ("builder_exit_address", 24), ("consolidation_request_address", 24), ("deposit_contract_address", 24), ("deposit_event_signature_hash", 32), ("empty_code_hash", 32), ("empty_trie_root", 32), ("evm_empty", 8), ("evm_key_buf", 32), ("hdr_zero8", 8), ("history_storage_address", 24), ("keccak_pad", 136), ("keccak_rc", 192), ("keccak_st", 200), ("mpt_hash_scratch", 40), ("mpt_key_scratch", 16), ("mpt_nib_scratch", 64), ("null_address", 24), ("pre_hdr_buf", 96), ("rmd_h", 40), ("rmd_pad", 128), ("rmd_tab", 160), ("rmd_x", 128), ("sha_pad", 128), ("sha_st", 64), ("sk_buf", 64), ("ssz_len_chunk", 32), ("ssz_offs", 64), ("transfer_topic", 32), ("ts", 72), ("u256_ws", 640), ("vm_system_address", 24), ("withdrawal_request_address", 24), ("ws", 40), ("zero32", 32)]

/-- The fixed objects: every global buffer (empty while its global is still `0`) and the journal
array. -/
def fixedObjects {F : Type} (s : PanSemStateFiniteExact 64 F) : List Ivl :=
  (globalBuffers.map fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) ++
    [(globN s "journal", 32 * globN s "journal_cap")]

def RootIn (S : List Nat) (v : Nat) : Prop := v = 0 ∨ v ∈ S

/-- `S` is a set of well-formed, allocated tables with pairwise disjoint footprints, disjoint
from the fixed objects; it contains every root and is closed under the two nested roots. -/
def TablesTyped {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat) : Prop :=
  S.Nodup ∧
  (∀ t ∈ S, HtabWF s t ∧ ∀ i ∈ htabFootprint s t, Allocated s i ∧
    ∀ j ∈ fixedObjects s, Disj i j) ∧
  (∀ t ∈ S, ∀ u ∈ S, t ≠ u → ∀ i ∈ htabFootprint s t, ∀ j ∈ htabFootprint s u, Disj i j) ∧
  (∀ k ∈ wsTableSlots, globN s "ws" ≠ 0 → RootIn S (memW s (globN s "ws" + k))) ∧
  (∀ k ∈ bsTableSlots, globN s "bs" ≠ 0 → RootIn S (memW s (globN s "bs" + k))) ∧
  (∀ k ∈ tsTableSlots, globN s "ts" ≠ 0 → RootIn S (memW s (globN s "ts" + k))) ∧
  (∀ g ∈ globalTableRoots, RootIn S (globN s g)) ∧
  (globN s "bs" ≠ 0 → memW s (globN s "bs" + 32) ∈ S → HtabValuesIn s (memW s (globN s "bs" + 32)) S) ∧
  (globN s "ts" ≠ 0 → memW s (globN s "ts" + 32) ∈ S → HtabValuesIn s (memW s (globN s "ts" + 32)) S)

/-- The journal: `journal_n ≤ journal_cap ≤ 2^19`, the array is allocated, and every record's
table (`+0`) is a typed table (`state_restore` calls `htab_set`/`htab_del` on it). -/
def JournalTyped {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat) : Prop :=
  globN s "journal_n" ≤ globN s "journal_cap" ∧ globN s "journal_cap" ≤ journalCapMax ∧
  (globN s "journal_cap" = 0 ∨ (Allocated s (globN s "journal", 32 * globN s "journal_cap") ∧
    WordsOK s (globN s "journal", 32 * globN s "journal_cap"))) ∧
  ∀ i, i < globN s "journal_n" → memW s (globN s "journal" + 32 * i) ∈ S

/-- The fixed objects are allocated words and pairwise disjoint. -/
def FixedTyped {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  (∀ i ∈ fixedObjects s, i.2 = 0 ∨ (Allocated s i ∧ WordsOK s i)) ∧ (fixedObjects s).Pairwise Disj

/-! ### MPT node heap -/

/-- Trie nodes are 176-byte records (`node_new_*`): kind at `+0` (`2` extension with child `+48`,
`3` branch with children `+32 + 8i`, `i < 16`), cached encoding `+8/+16`, branch value
`+160/+168`. `NodeHeap s Nd`: the nodes `Nd` are allocated heap records, pairwise disjoint, and
closed under children. -/
def NodeHeap {F : Type} (s : PanSemStateFiniteExact 64 F) (Nd : List Nat) : Prop :=
  (∀ n ∈ Nd, Allocated s (n, 176) ∧ Inside (n, 176) sourceBase heapLimit ∧ WordsOK s (n, 176) ∧
    (memW s n = 2 → RootIn Nd (memW s (n + 48))) ∧
    (memW s n = 3 → ∀ i, i < 16 → RootIn Nd (memW s (n + 32 + 8 * i)))) ∧
  (∀ n ∈ Nd, ∀ m ∈ Nd, n ≠ m → Disj (n, 176) (m, 176))

/-- The persistent tries: the witness state trie `ws+24` and the cached storage tries (live
values `v` of table `ws+32` are root nodes tagged `+1`, `ws_storage_trie` 13042) are typed node
heaps, disjoint from every typed table and fixed object (`compute_state_root` mutates them through
`mpt_set`). -/
def TriesTyped {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat) : Prop :=
  ∃ Nd : List Nat, NodeHeap s Nd ∧
    (∀ n ∈ Nd, (∀ t ∈ S, ∀ i ∈ htabFootprint s t, Disj (n, 176) i) ∧
      ∀ j ∈ fixedObjects s, Disj (n, 176) j) ∧
    (globN s "ws" ≠ 0 → RootIn Nd (memW s (globN s "ws" + 24)) ∧
      (memW s (globN s "ws" + 32) ∈ S → ∀ i, i < hdr s (memW s (globN s "ws" + 32)) 3 →
        RootIn Nd (nodeF s (hdr s (memW s (globN s "ws" + 32)) 5)
          (memW s (hdr s (memW s (globN s "ws" + 32)) 6 + 8 * i)) 8 - 1)))

/-- The global invariant of the guarded tier between EVM frames. -/
def WorldTyped {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat) : Prop :=
  TablesTyped s S ∧ JournalTyped s S ∧ FixedTyped s ∧ TriesTyped s S

def WorldOK : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ ∃ S : List Nat, WorldTyped s S

/-! ### EVM frames (round-1 item 5)

Frame record `e` (280 B, `frame_new` 15370): `+0` pc, `+8` stack base, `+16` stack height,
`+24/+32/+40` memory base/length/capacity, `+48/+56` code/length, `+64` gas, `+72` state gas,
`+80` jump-destination bitmap, `+88` logs list, `+104` running flag, `+112` message, `+120/+128`
output, `+136` deletion table, `+144/+152/+216` return-data buffer/length/capacity, `+160` error,
`+168/+176` access tables, `+192` spilled gas, `+208/+224` marks, `+232` stack capacity,
`+264/+272` access counts. Continuation record `c` (104 B, `frame_open` 18450, `start_child`
18705): `+0` parent frame, `+8` parent continuation, `+16` kind (`0` = outermost), `+24` journal
snapshot, `+32` done flag, `+40` message, `+48/+56` scratch / frame-memory marks released by
`finish_child`, `+64` new-account flag, `+72/+80` output window in the PARENT's memory, `+88`
contract address, `+96` create snapshot. DESIGN.md Q1 audits every pointer field. -/

/-- The active chain `(ev, cur_cont), (parent ev, parent cont), …`, following `c+0`/`c+8` while
the kind `c+16 ≠ 0` (exactly the `run_frames` / `finish_child` control flow). -/
def evmChainFrom {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat → Nat → Nat → List Ivl
  | 0, _, _ => []
  | fuel + 1, e, c =>
    (e, c) :: (if memW s (c + 16) = 0 then [] else evmChainFrom s fuel (memW s c) (memW s (c + 8)))

def evmChain {F : Type} (s : PanSemStateFiniteExact 64 F) : List Ivl :=
  evmChainFrom s (maxChain + 1) (globN s "ev") (globN s "cur_cont")

/-- The current frame cannot run another instruction (`run_frames` 18675-18681). -/
abbrev EvmDone {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  memW s (globN s "cur_cont" + 32) ≠ 0 ∨ memW s (globN s "ev" + 104) = 0 ∨
    memW s (globN s "ev" + 56) ≤ memW s (globN s "ev")

/-- The logs backing array of frame `e`: header `h = e+88` holds data `+0`, length `+8`, capacity
`+16`; elements are 8-byte log pointers (`frame_new` 15407: `lst_new_scratch(8, 4)`). It starts in
scratch and `lst_push` (13842) regrows it on the HEAP (round-2 Astra item 5). -/
def frameLogs {F : Type} (s : PanSemStateFiniteExact 64 F) (ec : Ivl) : Ivl :=
  (memW s (memW s (ec.1 + 88)), 8 * memW s (memW s (ec.1 + 88) + 16))

/-- The return-data buffer of frame `e` (round-3 item 4): pointer `e+144`, capacity `e+216`.
`set_retdata` (19064) writes `n ≤ cap` bytes at the pointer, and when `cap < n` replaces it by
`alloc(n + 8)`, a heap block of `round8 (n + 8)` bytes. With capacity `0` nothing is ever written
through the pointer (`n = 0` returns early, `n > 0` reallocates); it is then `evm_empty`
(`frame_new` 15431, `set_retdata` 19074) and the block is empty, `(0, 0)`. -/
def frameRet {F : Type} (s : PanSemStateFiniteExact 64 F) (ec : Ivl) : Ivl :=
  if memW s (ec.1 + 216) = 0 then (0, 0)
  else (memW s (ec.1 + 144), (memW s (ec.1 + 216) + 15) / 8 * 8)

/-- The memory blocks a frame writes: record, continuation, stack, EVM memory, logs header, logs
backing array, return-data buffer. Index 3 (EVM memory) lives in the frame-memory arena, index 5
(logs array) in the heap or scratch, index 6 (return data, round-3 item 4) in the heap, the others
in scratch. -/
def frameObjects {F : Type} (s : PanSemStateFiniteExact 64 F) (ec : Ivl) : List Ivl :=
  [(ec.1, 280), (ec.2, 104), (memW s (ec.1 + 8), 32 * memW s (ec.1 + 232)),
   (memW s (ec.1 + 24), memW s (ec.1 + 40)), (memW s (ec.1 + 88), 24), frameLogs s ec,
   frameRet s ec]

/-- The scratch-resident blocks of a frame (`frameObjects` without EVM memory and logs array). -/
def frameScratch {F : Type} (s : PanSemStateFiniteExact 64 F) (ec : Ivl) : List Ivl :=
  [(ec.1, 280), (ec.2, 104), (memW s (ec.1 + 8), 32 * memW s (ec.1 + 232)),
   (memW s (ec.1 + 88), 24)]

/-- One frame: record, continuation, stack and logs header in allocated scratch; EVM memory in
the frame-memory arena below `frame_mem_ptr`; logs backing array in allocated heap or scratch;
return-data buffer in allocated heap, or capacity `0` with pointer `evm_empty`;
`1 ≤` stack capacity (round-3 item 3: `PUSH0` on capacity `0` made `stack_push` allocate a
0-word stack and store past it), stack height ≤ capacity ≤ 1024, memory length ≤ capacity,
`1 ≤` logs capacity (round-3 item 3: `lst_push` on capacity `0` regrows to `0` and sets length 1),
logs length ≤ capacity; its three tables are typed. `frame_new` gives capacities 32 and 4;
`stack_push` (15080) doubles up to 1024 and `lst_push` (13856) doubles, so both stay `≥ 1`. -/
def FrameWF {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat) (ec : Ivl) : Prop :=
  let e := ec.1
  (∀ i ∈ [(e, 280), (ec.2, 104), (memW s (e + 8), 32 * memW s (e + 232)), (memW s (e + 88), 24)],
    Inside i (globN s "scratch_ptr") scratchEnd ∧ WordsOK s i) ∧
  Inside (memW s (e + 24), memW s (e + 40)) scratchStart (globN s "frame_mem_ptr") ∧
  WordsOK s (memW s (e + 24), memW s (e + 40)) ∧
  1 ≤ memW s (e + 232) ∧ memW s (e + 16) ≤ memW s (e + 232) ∧ memW s (e + 232) ≤ 1024 ∧
  memW s (e + 32) ≤ memW s (e + 40) ∧
  memW s (e + 136) ∈ S ∧ memW s (e + 168) ∈ S ∧ memW s (e + 176) ∈ S ∧
  1 ≤ memW s (memW s (e + 88) + 16) ∧
  memW s (memW s (e + 88) + 8) ≤ memW s (memW s (e + 88) + 16) ∧
  (Inside (frameLogs s ec) sourceBase (globN s "heap_ptr") ∨
    Inside (frameLogs s ec) (globN s "scratch_ptr") scratchEnd) ∧
  WordsOK s (frameLogs s ec) ∧
  ((memW s (e + 216) = 0 ∧ memW s (e + 144) = globN s "evm_empty") ∨
    (Inside (frameRet s ec) sourceBase (globN s "heap_ptr") ∧ WordsOK s (frameRet s ec)))

/-- A suspended frame has room for one more stack word (round-2 item 2). `finish_child`
(`Guest/SoftwareAst.lean:18572`) runs `stack_push` on the parent BEFORE
`scratch_release(child_mark)`; on a full parent `stack_push` would allocate a new 64-slot stack
below the child's mark, which the release then frees. Every frame below the current one was
suspended by one of the six frame-opening opcodes (`op_call`, `op_callcode`, `op_delegatecall`,
`op_staticcall` pop 6 or 7 words and push at most one; `op_create`, `op_create2` pop 3 or 4) after
those pops, so `op_dispatch_spec` re-establishes it for the new parent. -/
def FrameRoom {F : Type} (s : PanSemStateFiniteExact 64 F) (ec : Ivl) : Prop :=
  memW s (ec.1 + 16) + 1 ≤ memW s (ec.1 + 232)

/-- Output windows of the suspended frames (round-3 item 4). `finish_child` (18650-18652) copies
`min(c+80, child+128)` bytes to `parent_mem + c+72`, where `c` is the child's continuation and
`parent_mem`, `parent_mem + capacity` are the parent's `e+24`, `e+40`. So for every chain position
`i` with a parent, either the window is empty (`c_i+80 = 0`: `op_call` passes
`sat_word(out_start)`, which is arbitrary when the size is `0`, so the sum need not be in range)
or it lies inside the parent's EVM memory. `op_call`/`op_callcode`/`op_delegatecall`/
`op_staticcall` establish it by `extend_memory` on the output window BEFORE `generic_call` →
`start_child` stores the window (18746-18748); `op_create`/`op_create2` store size `0`. The parent
is suspended, so nothing changes its memory capacity until `finish_child`. -/
def RetWindowsOK {F : Type} (s : PanSemStateFiniteExact 64 F) (ch : List Ivl) : Prop :=
  ∀ (i : Nat) (hi : i + 1 < ch.length),
    memW s ((ch[i]'(by omega)).2 + 80) = 0 ∨
      memW s ((ch[i]'(by omega)).2 + 72) + memW s ((ch[i]'(by omega)).2 + 80) ≤
        memW s (ch[i + 1].1 + 40)

/-- Release marks of the child at chain position `i` (whose continuation is `c_i`): releasing
scratch to `c_i+48` and frame memory to `c_i+56` frees exactly the child's scratch blocks and keeps
every ancestor's blocks allocated (an ancestor's logs array is on the heap or above the mark). -/
def MarksOK {F : Type} (s : PanSemStateFiniteExact 64 F) (ch : List Ivl) : Prop :=
  ∀ (i : Nat) (hi : i + 1 < ch.length),
    let m := memW s ((ch[i]'(by omega)).2 + 48)
    let mm := memW s ((ch[i]'(by omega)).2 + 56)
    m ≤ scratchEnd ∧ scratchStart ≤ mm ∧
    (∀ j (hj : j < ch.length), i < j →
      (∀ o ∈ frameScratch s ch[j], Inside o m scratchEnd) ∧
      Inside (frameObjects s ch[j])[3]! scratchStart mm ∧
      (Inside (frameLogs s ch[j]) sourceBase heapLimit ∨ Inside (frameLogs s ch[j]) m scratchEnd)) ∧
    (∀ o ∈ frameScratch s (ch[i]'(by omega)), o.1 + o.2 ≤ m) ∧
    mm ≤ memW s ((ch[i]'(by omega)).1 + 24)

/-- The EVM invariant at every `run_frames` loop head (replaces round 1's `EvmFramesWF`): the
world is typed (one table set `S` covering global AND frame tables), the chain is closed (its
last continuation has kind `0`) and at most `maxChain` long, every frame is well formed, every
suspended frame (`ch.tail`) has stack room for the result `finish_child` pushes (`FrameRoom`), every
child's output window lies in its parent's EVM memory (`RetWindowsOK`, round-3 item 4), all
frame blocks (return-data buffers included) are pairwise disjoint and disjoint from every table
footprint and fixed object, and the release marks are valid. There is NO gas conjunct: the potential `evmPot` is bounded for
arbitrary gas words. -/
def EvmInv : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ ∃ S : List Nat, WorldTyped s S ∧
    let ch := evmChain s
    ch ≠ [] ∧ ch.length ≤ maxChain ∧ (∃ ec ∈ ch.getLast?, memW s (ec.2 + 16) = 0) ∧
    (∀ ec ∈ ch, FrameWF s S ec) ∧ (∀ ec ∈ ch.tail, FrameRoom s ec) ∧ RetWindowsOK s ch ∧
    ((ch.map (frameObjects s)).flatten).Pairwise Disj ∧
    (∀ ec ∈ ch, ∀ o ∈ frameObjects s ec,
      (∀ t ∈ S, ∀ i ∈ htabFootprint s t, Disj o i) ∧ ∀ j ∈ fixedObjects s, Disj o j) ∧
    MarksOK s ch

/-! Round-1 item 5 regressions, by construction of `EvmInv`/`evmPot`:
* minting gas (`refill_frame_state_gas` with `spilled = 2^62`, `incorporate_child_on_error`) can
  only move gas between the `R` and `S` components of `evmPot`, whose ranges are bounded by the
  word size, not by any gas invariant;
* `ev+8 = ev` (stack over the record) violates the pairwise disjointness of `frameObjects`;
* a wild `cur_cont+48` violates `MarksOK`. -/

def evmPotS : Nat := maxChain * 2 ^ 64
def evmPotF : Nat := 2 * maxChain + 2

/-- Lexicographic EVM potential `(R, F, S)` as one number:
`R = Σ (gas + spilled)` over the chain, `F = 2·depth + [not done]`, `S = Σ state gas`.
Every word is `< 2^64` and `depth ≤ maxChain`, so `F < evmPotF`, `S < evmPotS` and
`evmPot < evmPotMax` for ARBITRARY gas contents. A continuing `run_frames` iteration
* charges regular gas (`R` drops; `CALL` moves gas to the child without changing `R`), or
* charges only state gas (`S` drops, `R`, `F` unchanged), or
* halts the frame (`F` drops by one; `refill_frame_state_gas` keeps `R` and may raise `S`), or
* pops a done frame (`finish_child`: `F` drops by at least one; `incorporate_child_on_*` adds
  the child's `gas (+ spilled)` to the parent, so `R` does not grow; state-gas refunds only
  raise `S`). -/
def evmPot {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  let ch := evmChain s
  let R := (ch.map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum
  let Fp := 2 * ch.length + (if EvmDone s then 0 else 1)
  let S := (ch.map fun ec => memW s (ec.1 + 72)).sum
  R * (evmPotF * evmPotS) + Fp * evmPotS + S

def evmPotMax : Nat := (2 * maxChain * 2 ^ 64 + 1) * evmPotF * evmPotS

/-- The `run_frames` loop (`while go != 0 …`, `Guest/SoftwareAst.lean:18672`), read off the
installed code. -/
def runFramesLoop : Option (ExpHOL 64 × ProgHOL 64) :=
  match originalRuntimeCode.lookup (ofString "run_frames") with
  | some (_, .dec _ _ _ (.seq (.while c b) _), _) => some (c, b)
  | _ => none
