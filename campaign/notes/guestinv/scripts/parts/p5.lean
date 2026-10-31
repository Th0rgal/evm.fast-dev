
/-! ## 7. Guarded tier: contracts and leaves

The six loops without an arbitrary-memory measure (`run_frames`, `htab_truncate`,
`_decode_witness_node_body`, `_mpt_insert_node`, `_mpt_delete_node_body` ×2) and every function
that (transitively) calls one of them. Each such function has a bound leaf under an explicit
guard (the generated `gb_*` leaves below and DESIGN.md §6); the memory facts those leaves need at
their guarded call sites are the contracts of this section, each a separate leaf. Every guard is
`LocalsOnly` (end of this section), so `dec_onLocals`, `LocalsOnly.decClock` (`hdec` of the
`while` rules) and `decCall_on` apply to it. -/

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

/-! ### Table contracts (round-1 items 3 and 4) -/

theorem htab_set_spec : FunSpec HtabArgWF (OnReturn HtabExit) (ofString "htab_set") := by sorry
theorem htab_del_spec : FunSpec HtabArgWF (OnReturn HtabExit) (ofString "htab_del") := by sorry

/-- Progress of `htab_del` (round-2 item 3, `htab_truncate`): a normal return either deleted a
leaf, so the count `t+24` dropped by one, or wrote nothing at all (`htab_find_leaf` found no leaf
or `memeq` rejected its key; `HtabWF` does not constrain key bytes, so the key of the last leaf
need not lead back to that leaf). In the second case memory, globals and the FFI state are those of
the entry state: the caller's loop head repeats exactly (`SameHead`). -/
def HtabDelProgress : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F →
    Prop :=
  fun s post => hdr post (locN s "t") 3 + 1 = hdr s (locN s "t") 3 ∨
    post = { s with locals := post.locals, clock := post.clock }

theorem htab_del_progress_spec :
    FunSpec HtabArgWF (OnReturn HtabDelProgress) (ofString "htab_del") := by sorry
theorem htab_truncate_spec :
    FunSpec HtabArgWF (OnReturn HtabExit) (ofString "htab_truncate") := by sorry
theorem htab_union_into_spec :
    FunSpec UnionArgWF (OnReturn UnionExit) (ofString "htab_union_into") := by sorry

/-- `htab_new` / `htab_new_scratch` return a well-formed empty table whose footprint is freshly
allocated (heap resp. scratch); nothing outside the UNION of the fresh heap and the fresh scratch
changes (round-2 Astra item 2: revision 2 intersected the two frames), and no global but the two
allocator pointers changes (round-3 Gemini item 5: the globals frame was missing). -/
def HtabNewExit : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
    PanSemStateFiniteExact 64 F → Prop :=
  fun s r post => ∀ v, r = some (.returned v) → ∃ w : BitVec 64, v = .val (.word w) ∧
    ArenaReady post ∧ HtabWF post w.toNat ∧ hdr post w.toNat 3 = 0 ∧
    (∀ i ∈ htabFootprint post w.toNat, Allocated post i ∧
      (Inside i (globN s "heap_ptr") (globN post "heap_ptr") ∨
        Inside i (globN post "scratch_ptr") (globN s "scratch_ptr"))) ∧
    FrameOutside s post
      [(globN post "scratch_ptr", globN s "scratch_ptr" - globN post "scratch_ptr")]
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") ∧
    ∀ name, name ∉ ["heap_ptr", "scratch_ptr"] →
      s.globals.lookup (ofString name) = post.globals.lookup (ofString name)

/-- Entry of `htab_new` / `htab_new_scratch` (round-2 Fable item 1, Astra item 3): separated
arenas, a key length from the literal call sites and a bounded capacity. `htab_new` checks
neither: `key_len = 0` breaks `1 ≤ klen`, `61` breaks `klen ≤ maxKeyLen`, `2^64 - 3` wraps the
stride; `cap = 2^64 - 1` wraps `(ncap + 1) * stride`. 31 call sites pass a literal capacity
(≤ 256); `nodedb_build` passes a power of two, which its caller bounds (round-3 non-blocking). -/
def HtabNewReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ locN s "key_len" ∈ htabKeyLens ∧ locN s "cap" ≤ htabCapMax

theorem htab_new_spec : FunSpec HtabNewReady HtabNewExit (ofString "htab_new") := by sorry
theorem htab_new_scratch_spec :
    FunSpec HtabNewReady HtabNewExit (ofString "htab_new_scratch") := by sorry

/-! ### MPT update contracts (`_mpt_insert_node`, `_mpt_delete_node_body`) -/

/-- Entry of the two MPT update functions: separated arenas and a typed trie below the `node`
parameter. -/
def MptReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ ∃ Nd, NodeHeap s Nd ∧ RootIn Nd (locN s "node")

/-- The trie object `m` (16 bytes, `mpt_new` 10446: `+0` root node) and its node set, placed
relative to the typed world `S` (revision 5, round-4 Fable item 3): `m` is allocated, and `m` and
every node of `Nd` are disjoint from every table footprint of `S` and every fixed object, as
`TriesTyped` requires of the world tries. `mpt_set` stores `m+0` (10886) and rewrites node records;
`mpt_root` stores hash pointers into the node caches (`+8/+16`). A node at `nodes + 8` of a table
in `S` made `mpt_root` overwrite that table's root. -/
def MptObjIn {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat) : Prop :=
  Allocated s (locN s "m", 16) ∧ WordsOK s (locN s "m", 16) ∧
  (∀ t ∈ S, ∀ i ∈ htabFootprint s t, Disj (locN s "m", 16) i) ∧
  (∀ j ∈ fixedObjects s, Disj (locN s "m", 16) j) ∧
  ∃ Nd, NodeHeap s Nd ∧ RootIn Nd (memW s (locN s "m")) ∧
    ∀ n ∈ Nd, Disj (nodeIvl s n) (locN s "m", 16) ∧
      (∀ t ∈ S, ∀ i ∈ htabFootprint s t, Disj (nodeIvl s n) i) ∧
      ∀ j ∈ fixedObjects s, Disj (nodeIvl s n) j

/-- A typed world `S` with a typed trie object `m` in it (`MptObjIn`, the same `S`), and regions
`R s` disjoint from every table footprint of `S` and every fixed object (`mpt_root`'s output
buffer, as in `WorldAvoids`). -/
def MptObjAvoids (R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ ∃ S, WorldTyped s S ∧ MptObjIn s S ∧ ∀ i ∈ R s,
    (∀ t ∈ S, ∀ j ∈ htabFootprint s t, Disj i j) ∧ ∀ j ∈ fixedObjects s, Disj i j

/-- `mpt_set(m, …)`: a typed world with the trie object `m` in it (revision 5: `MptObjIn`; the
revision-4 guard did not relate `m` and its nodes to the typed tables and fixed objects). -/
def MptObjReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => MptObjAvoids (fun _ => []) s

/-- Exit: the returned root is typed in the new node heap, which extends the old one by fresh
heap records; old memory outside the old nodes (sized by kind), the heap free at entry and the
scratch free at entry is unchanged, and only `heap_ptr`/`scratch_ptr` among the globals change.
Round-3 Gemini item 5: nodes are sized by kind (`nodeIvl`), and `_mpt_delete_node_body` leaves
40-byte `scratch_alloc` frames below the entry `scratch_ptr` (its caller releases them), so the
free scratch gap `[frame_mem_ptr, scratch_ptr)` at entry is in the frame; the globals frame was
missing. -/
def MptExit : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
    PanSemStateFiniteExact 64 F → Prop :=
  fun s r post => ∀ v, r = some (.returned v) → ∃ w : BitVec 64, v = .val (.word w) ∧
    ArenaReady post ∧ globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
    (∀ name, name ∉ ["heap_ptr", "scratch_ptr"] →
      s.globals.lookup (ofString name) = post.globals.lookup (ofString name)) ∧
    ∃ Nd Nd', NodeHeap s Nd ∧ RootIn Nd (locN s "node") ∧ NodeHeap post Nd' ∧
      RootIn Nd' w.toNat ∧
      FrameOutside s post
        ((Nd.map fun n => nodeIvl s n) ++
          [(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")])
        (globN s "heap_ptr", heapLimit - globN s "heap_ptr")

theorem mpt_insert_node_spec : FunSpec MptReady MptExit (ofString "_mpt_insert_node") := by sorry
theorem mpt_delete_node_body_spec :
    FunSpec MptReady MptExit (ofString "_mpt_delete_node_body") := by sorry

/-! ### `WorldOK` from `mem_init` -/

/-- After `mem_init` the arenas are separated and every root is `0` (all globals were `0`). -/
theorem mem_init_world :
    FunSpec (fun s => GuestInv s ∧ GlobalsZero s) (OnReturn fun _ post => WorldOK post)
      (ofString "mem_init") := by sorry

/-! ### EVM frame contracts (round-1 item 5) -/

/-- `R` component of `evmPot`. -/
def evmR {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  ((evmChain s).map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum

def IsEvmErr (r : Option (PanSemResultExact 64)) : Prop :=
  ∃ v, r = some (.exception (ofString "EvmErr") v)

/-- One instruction: from a running frame, a normal return strictly lowers `evmPot` (charged
regular or state gas, or halted the frame); an `EvmErr` leaves the chain length and `R` no larger
(the handler `frame_exception` then halts the frame). -/
theorem op_dispatch_spec :
    FunSpec (fun s => EvmInv s ∧ ¬ EvmDone s)
      (fun s r post =>
        ((∃ v, r = some (.returned v)) → EvmInv post ∧ evmPot post < evmPot s) ∧
        (IsEvmErr r → EvmInv post ∧ (evmChain post).length = (evmChain s).length ∧
          evmR post ≤ evmR s))
      (ofString "op_dispatch") := by sorry

/-- The `EvmErr` handler halts the current frame (`cur_cont+32 := 1`) without growing `R`. -/
theorem frame_exception_spec :
    FunSpec EvmInv
      (OnReturn fun s post => EvmInv post ∧ EvmDone post ∧
        (evmChain post).length = (evmChain s).length ∧ evmR post ≤ evmR s)
      (ofString "frame_exception") := by sorry

/-- The epilogue only rolls back the journal (tables in the typed set). -/
theorem frame_epilogue_spec :
    FunSpec (fun s => EvmInv s ∧ EvmDone s)
      (OnReturn fun s post => EvmInv post ∧ EvmDone post ∧
        (evmChain post).length = (evmChain s).length ∧ evmR post ≤ evmR s)
      (ofString "frame_epilogue") := by sorry

/-- Popping a done child: one frame shorter, `R` not larger, on return and on `EvmErr` (raised,
if at all, after the pop by `stack_push` in the parent). Includes the marks release
(`MarksOK`), `rollback_child_access` (truncation of the child's typed access tables) and
`incorporate_child_on_success` (`htab_union_into` into the parent's typed table). -/
theorem finish_child_spec :
    FunSpec (fun s => EvmInv s ∧ EvmDone s ∧ memW s (globN s "cur_cont" + 16) ≠ 0)
      (fun s r post => ((∃ v, r = some (.returned v)) ∨ IsEvmErr r) →
        EvmInv post ∧ (evmChain post).length + 1 = (evmChain s).length ∧ evmR post ≤ evmR s)
      (ofString "finish_child") := by sorry

/-! ### Guards of the guarded bound leaves -/

/-- `op_dispatch`, `op_sload`, `op_sstore` entry (revision 5, round-4 Fable item 1): a running
frame, the precondition of `op_dispatch_spec`, which `run_frames` provides at its `op_dispatch`
call. `charge_gas`, `stack_pop` and `warm_storage_key` write through the global `ev` (the frame's
gas, stack and access table), which `WorldOK` does not own; `EvmInv` does (`frameObjects`). -/
def EvmRun : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => EvmInv s ∧ ¬ EvmDone s

/-- `finish_child` entry (inside `run_frames`). -/
def FinishReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => EvmInv s ∧ EvmDone s ∧ memW s (globN s "cur_cont" + 16) ≠ 0

/-- `rollback_child_access(child)`: the child's two access tables are typed. -/
def RollbackReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ ∀ k ∈ [168, 176],
    HtabWF s (memW s (locN s "child" + k)) ∧
    ∀ i ∈ htabFootprint s (memW s (locN s "child" + k)), Allocated s i

/-! ### Every guard reads at most one local (`dec_onLocals`, round-2 item 3) -/

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

theorem tablesTyped_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (S : List Nat) :
    TablesTyped { s with locals := locals, clock := k } S ↔ TablesTyped s S := by
  simp only [TablesTyped, htabWF_with_locals]
  exact Iff.rfl

theorem worldTyped_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (S : List Nat) :
    WorldTyped { s with locals := locals, clock := k } S ↔ WorldTyped s S := by
  simp only [WorldTyped, tablesTyped_with_locals]
  exact Iff.rfl

theorem locN_congr {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (n : String)
    (h : locals.lookup (ofString n) = s.locals.lookup (ofString n)) :
    locN { s with locals := locals, clock := k } n = locN s n := by
  simp only [locN, h]

theorem arenaReady_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    ArenaReady { s with locals := locals, clock := k } ↔ ArenaReady s :=
  ⟨fun h => ⟨guestInv_congr (s := { s with locals := locals, clock := k }) rfl rfl rfl rfl h.1, h.2⟩,
   fun h => ⟨guestInv_with_locals_clock s locals k h.1, h.2⟩⟩

theorem evmChainFrom_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    ∀ (fuel e c : Nat),
      evmChainFrom { s with locals := locals, clock := k } fuel e c = evmChainFrom s fuel e c
  | 0, _, _ => rfl
  | fuel + 1, e, c => by
    simp only [evmChainFrom, evmChainFrom_with_locals s locals k fuel]
    rfl

theorem evmChain_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    evmChain { s with locals := locals, clock := k } = evmChain s :=
  evmChainFrom_with_locals s locals k _ _ _

theorem localsFree_arenaReady : LocalsFree ArenaReady :=
  fun s locals k h => (arenaReady_with_locals s locals k).2 h

theorem localsFree_worldOK : LocalsFree WorldOK := by
  intro F s locals k h
  simp only [WorldOK, worldTyped_with_locals, arenaReady_with_locals] at h ⊢
  exact h

theorem localsFree_evmInv : LocalsFree EvmInv := by
  intro F s locals k h
  simp only [EvmInv, worldTyped_with_locals, arenaReady_with_locals, evmChain_with_locals] at h ⊢
  exact h

/-- Round-3 non-blocking: `main`'s guard reads neither locals nor the clock. -/
theorem localsFree_mainEntry : LocalsFree MainEntry := by
  intro F s locals k h
  obtain ⟨⟨hg, hc⟩, hm, hz⟩ := h
  exact ⟨⟨guestInv_with_locals_clock s locals k hg, hc⟩, hm, hz⟩

theorem localsOnly_mainEntry : LocalsOnly [] MainEntry :=
  LocalsOnly.of_localsFree localsFree_mainEntry

theorem localsFree_finishReady : LocalsFree FinishReady := by
  intro F s locals k h
  exact ⟨localsFree_evmInv s locals k h.1, h.2⟩

theorem localsFree_evmRun : LocalsFree EvmRun := by
  intro F s locals k h
  exact ⟨localsFree_evmInv s locals k h.1, h.2⟩

theorem localsOnly_htabArgWF : LocalsOnly ["t"] HtabArgWF := by
  intro F s locals k hl hP
  have ht := locN_congr s locals k "t" (hl "t" (by simp))
  simp only [HtabArgWF, htabWF_with_locals, arenaReady_with_locals] at hP ⊢
  rw [ht]
  exact hP

theorem localsOnly_unionArgWF : LocalsOnly ["dst"] UnionArgWF := by
  intro F s locals k hl hP
  have ht := locN_congr s locals k "dst" (hl "dst" (by simp))
  simp only [UnionArgWF, htabWF_with_locals, arenaReady_with_locals] at hP ⊢
  rw [ht]
  exact hP

theorem localsOnly_mptReady : LocalsOnly ["node"] MptReady := by
  intro F s locals k hl hP
  have ht := locN_congr s locals k "node" (hl "node" (by simp))
  simp only [MptReady, arenaReady_with_locals] at hP ⊢
  rw [ht]
  exact hP

theorem localsOnly_mptObjReady : LocalsOnly ["m"] MptObjReady := by
  intro F s locals k hl hP
  have ht := locN_congr s locals k "m" (hl "m" (by simp))
  simp only [MptObjReady, MptObjAvoids, MptObjIn, worldTyped_with_locals, arenaReady_with_locals]
    at hP ⊢
  rw [ht]
  exact hP

theorem localsOnly_rollbackReady : LocalsOnly ["child"] RollbackReady := by
  intro F s locals k hl hP
  have ht := locN_congr s locals k "child" (hl "child" (by simp))
  simp only [RollbackReady, htabWF_with_locals, arenaReady_with_locals] at hP ⊢
  rw [ht]
  exact hP

theorem localsOnly_htabNewReady : LocalsOnly ["key_len", "cap"] HtabNewReady := by
  intro F s locals k hl hP
  have ht := locN_congr s locals k "key_len" (hl "key_len" (by simp))
  have hc := locN_congr s locals k "cap" (hl "cap" (by simp))
  simp only [HtabNewReady, arenaReady_with_locals] at hP ⊢
  rw [ht, hc]
  exact hP

/-- Regression for `dec_onLocals`: `htab_truncate`'s body declares `stride`, `pos`, `leaf`, never
`t`, so `HtabArgWF` passes every `dec` of the body. -/
example : ∀ n ∈ ["t"], ofString n ≠ ofString "pos" := by decide

/-! ### Callee contracts for the guarded compositions (round-3 recommendation, item 5)

Each guarded body (`gbody_*`, below) is composed from its callees' bounds and, at every call site
that is followed by a guarded call or a guarded loop head (computed by `coverage.py`, DESIGN.md
§6), a contract that carries the caller's world guard across the call. A contract only speaks
about outcomes that resume the caller: a normal return, or an exception other than `TrapErr`
(`trap_with` is the only raiser of `TrapErr`, after its FFI call, and no handler in the program
catches it). Three uniform shapes, chosen mechanically:
* `ReadOnlyFn`: the callee (transitively) has no store, no global assignment and no FFI call
  (`trap_with` aside), so it changes nothing but its own locals and the clock;
* `WritesWithin R`: the callee writes only the region `R` (its pointer parameters' extents and the
  global scratch buffers it uses), memory that is free at entry (above `heap_ptr`, between
  `frame_mem_ptr` and `scratch_ptr`) and the allocator globals it lists; true for arbitrary
  states, the caller shows `R` is unowned;
* `KeepsOn P W`: from a `P` entry the callee ends in a `W` state (the reviewers'
  `PreservesOn WorldOK WorldOK`, restricted to resuming outcomes). -/

/-- The outcomes after which the caller resumes (return, or a catchable exception). -/
def Resumes (r : Option (PanSemResultExact 64)) : Prop :=
  (∃ v, r = some (.returned v)) ∨ ∃ e v, r = some (.exception e v) ∧ e ≠ ofString "TrapErr"

/-- `fname` changes nothing but locals and clock. -/
def ReadOnlyFn (fname : MlS) : Prop :=
  FunSpec GuestInv (fun s r post => Resumes r → post = { s with locals := post.locals, clock := post.clock })
    fname

/-- From a `P` entry, every resuming outcome is a `W` state. -/
def KeepsOn (P W : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop) (fname : MlS) : Prop :=
  FunSpec P (fun _ r post => Resumes r → W post) fname

/-- Write frame: on every resuming outcome the arenas stay separated and only grow, memory changes
only inside `R s` and the memory free at entry, and only the globals in `gw` change. -/
def WritesWithin (R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl) (gw : List String)
    (fname : MlS) : Prop :=
  FunSpec ArenaReady (fun s r post => Resumes r →
    ArenaReady post ∧ globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
    FrameOutside s post
      (R s ++ [(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")])
      (globN s "heap_ptr", heapLimit - globN s "heap_ptr") ∧
    ∀ name, name ∉ gw → s.globals.lookup (ofString name) = post.globals.lookup (ofString name))
    fname

/-- `WorldOK`, and the regions `R s` are disjoint from every typed table and fixed object. -/
def WorldAvoids (R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ ∃ S, WorldTyped s S ∧ ∀ i ∈ R s,
    (∀ t ∈ S, ∀ j ∈ htabFootprint s t, Disj i j) ∧ ∀ j ∈ fixedObjects s, Disj i j

/-- `process_transaction(tx, index)` writes the receipt slots `bo+24`/`bo+32` at `16·index`
(33368-33374): the index is below the block's transaction count `bo+80` (`execute_block`'s loop). -/
def TxReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => WorldOK s ∧ locN s "index" < memW s (globN s "bo" + 80)

/-- `execute_block(si, hdr)` (revision 5, round-4 non-blocking): the transaction count
`ntx = (si+0)+40` (33588) sizes the arrays `alloc(16·ntx + 16)` (33593, 33596) without wrapping,
so `blockOutObjects` (unwrapped length `16·(bo+80) + 16`) is the block `alloc` returns. -/
def BlockReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => WorldOK s ∧ 16 * memW s (memW s (locN s "si") + 40) + 16 < 2 ^ 64

theorem localsOnly_blockReady : LocalsOnly ["si"] BlockReady := by
  intro F s locals k hl hP
  have ht := locN_congr s locals k "si" (hl "si" (by simp))
  refine ⟨localsFree_worldOK s locals k hP.1, ?_⟩
  show 16 * memW s (memW s (locN { s with locals := locals, clock := k } "si") + 40) + 16 < 2 ^ 64
  rw [ht]; exact hP.2

/-- `process_general_purpose_requests` runs once per block, right after `execute_block` zeroed
`bo` (so no request is recorded yet); it appends at most three requests (`requests_append` 33485
writes slot `bo+64` of the 8-slot array `bo+56`). -/
def ReqsFresh : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => WorldOK s ∧ memW s (globN s "bo" + 64) = 0

/-- Entry of `process_message_call`, `process_create_message` and `process_message`: the world is
typed by a set `S` that contains the message's two access tables `msg+152`, `msg+160` (copied into
the outermost frame's `e+168`/`e+176` by `frame_new` 15418-15420). Every caller builds them with
`htab_new` just before (`process_transaction` 33343-33346, `process_unchecked_system_transaction`
32899-32902). Round-3 Gemini item 3: the 176-byte message record (`msg_new`) is owned, so the stores
`depth0_prepare`/`prepare_dispatch` make through it (`msg+48`, `+104`, `+112`, `+120`, `+168`)
cannot reach a table or fixed object; its gas `msg+40` (`mgas ≤ 16777216` after
`validate_transaction`, `30000000` for system calls) bounds the initial `R` of `EvmInv`. -/
def MsgReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ ∃ S, WorldTyped s S ∧
    memW s (locN s "msg" + 152) ∈ S ∧ memW s (locN s "msg" + 160) ∈ S ∧
    Allocated s (locN s "msg", 176) ∧ WordsOK s (locN s "msg", 176) ∧
    (∀ t ∈ S, ∀ i ∈ htabFootprint s t, Disj (locN s "msg", 176) i) ∧
    (∀ j ∈ fixedObjects s, Disj (locN s "msg", 176) j) ∧
    memW s (locN s "msg" + 40) < 2 ^ 63

/-- `frame_open(msg, 0)` in `process_message`: builds the outermost frame, after which `EvmInv`
holds (closed one-frame chain; its blocks are fresh scratch/frame memory; its tables are the
message's typed tables and a fresh `htab_new_scratch` table). -/
def FrameOpenReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => MsgReady s ∧ locN s "kind" = 0

theorem msgReady_worldOK {F : Type} (s : PanSemStateFiniteExact 64 F) (h : MsgReady s) :
    WorldOK s :=
  ⟨h.1, h.2.elim fun S hS => ⟨S, hS.1⟩⟩

theorem localsOnly_msgReady : LocalsOnly ["msg"] MsgReady := by
  intro F s locals k hl hP
  have hm := locN_congr s locals k "msg" (hl "msg" (by simp))
  simp only [MsgReady, worldTyped_with_locals, arenaReady_with_locals] at hP ⊢
  rw [hm]
  exact hP

theorem localsOnly_frameOpenReady : LocalsOnly ["msg", "kind"] FrameOpenReady := by
  intro F s locals k hl hP
  have hk := locN_congr s locals k "kind" (hl "kind" (by simp))
  refine ⟨localsOnly_msgReady s locals k (fun n hn => hl n (by simp at hn ⊢; exact Or.inl hn)) hP.1, ?_⟩
  show locN { s with locals := locals, clock := k } "kind" = 0
  rw [hk]; exact hP.2

/-- `EvmInv` with its table set `S` exposed (revision 5): the body of `EvmInv` after `∃ S`,
verbatim, so that a guard can state more facts about the same `S` (`evmInv_iff_at`, by `Iff.rfl`). -/
def EvmInvAt {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat) : Prop :=
  WorldTyped s S ∧
    let ch := evmChain s
    ch ≠ [] ∧ ch.length ≤ maxChain ∧ (∃ ec ∈ ch.getLast?, memW s (ec.2 + 16) = 0) ∧
    (∀ ec ∈ ch, FrameWF s S ec) ∧ (∀ ec ∈ ch.tail, FrameRoom s ec) ∧ RetWindowsOK s ch ∧
    ((ch.map (frameObjects s)).flatten).Pairwise Disj ∧
    (∀ ec ∈ ch, ∀ o ∈ frameObjects s ec,
      (∀ t ∈ S, ∀ i ∈ htabFootprint s t, Disj o i) ∧ ∀ j ∈ fixedObjects s, Disj o j) ∧
    MarksOK s S ch ∧
    (ch.map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum + 1 < 2 ^ 64

theorem evmInv_iff_at {F : Type} (s : PanSemStateFiniteExact 64 F) :
    EvmInv s ↔ ArenaReady s ∧ ∃ S, EvmInvAt s S := Iff.rfl

/-- The 176-byte message record at `m` is owned (as in `MsgReady`): allocated words, disjoint
from every table footprint of `S`, every fixed object and every frame block of the chain. -/
def MsgOwned {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat) (m : Nat) : Prop :=
  Allocated s (m, 176) ∧ WordsOK s (m, 176) ∧
  (∀ t ∈ S, ∀ i ∈ htabFootprint s t, Disj (m, 176) i) ∧
  (∀ j ∈ fixedObjects s, Disj (m, 176) j) ∧
  ∀ ec ∈ evmChain s, ∀ o ∈ frameObjects s ec, Disj (m, 176) o

/-- After `frame_open(msg, 0)` in `process_message` (revision 5, round-4 Fable item 2): `EvmInv`,
and the outermost frame's message `ev+112` (the `msg` of `MsgReady`, stored by `frame_new`) is
still owned, for the same table set. `depth0_prepare` stores `msg+48` (18772) and
`prepare_dispatch`, its only caller's callee, `msg+112`, `msg+120` (17836); `EvmInv` alone does not
own `ev+112` (a message at `t − 112` for a typed table `t` overwrote its key length). Only depth
`0` writes through the message, so `frameObjects` (all depths) is unchanged. -/
def EvmMsgReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ ∃ S, EvmInvAt s S ∧ MsgOwned s S (memW s (globN s "ev" + 112))

theorem evmInv_of_evmMsgReady {F : Type} (s : PanSemStateFiniteExact 64 F) (h : EvmMsgReady s) :
    EvmInv s :=
  ⟨h.1, h.2.elim fun S hS => ⟨S, hS.1⟩⟩

theorem localsFree_evmMsgReady : LocalsFree EvmMsgReady := by
  intro F s locals k h
  simp only [EvmMsgReady, EvmInvAt, MsgOwned, worldTyped_with_locals, arenaReady_with_locals,
    evmChain_with_locals] at h ⊢
  exact h

/-- MPT-tier callee entry (round-3 item 5, DESIGN.md Q9): separated arenas, and the listed node
parameters are rooted in a typed node heap. -/
def NodeArgs (names : List String) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ ∃ Nd, NodeHeap s Nd ∧ ∀ n ∈ names, RootIn Nd (locN s n)

/-- MPT-tier callee exit, `MptExit`-shaped: every typed node set rooting the node parameters
extends to a typed node set of the post-state; memory changes only inside those node records and
the heap free at entry; the returned word is a typed node or `0` (what `_mpt_insert_node` /
`_mpt_delete_node_body` need to re-establish `MptReady` at their loop heads). The node functions
write no global buffer (checked on their closures). -/
def NodeFnExit (names : List String) : ∀ {F : Type}, PanSemStateFiniteExact 64 F →
    Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop :=
  fun s r post => Resumes r → ArenaReady post ∧ globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
    ∀ Nd, NodeHeap s Nd → (∀ n ∈ names, RootIn Nd (locN s n)) →
      ∃ Nd', NodeHeap post Nd' ∧ (∀ n ∈ Nd, n ∈ Nd') ∧
        FrameOutside s post
          ((Nd.map fun n => nodeIvl s n) ++
            [(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")])
          (globN s "heap_ptr", heapLimit - globN s "heap_ptr") ∧
        (∀ name, name ∉ ["heap_ptr", "scratch_ptr"] →
          s.globals.lookup (ofString name) = post.globals.lookup (ofString name)) ∧
        ∀ v, r = some (.returned v) → ∃ w : BitVec 64, v = .val (.word w) ∧ RootIn Nd' w.toNat

def NodeFn (names : List String) (fname : MlS) : Prop :=
  FunSpec (NodeArgs names) (NodeFnExit names) fname

/-- `requests_append` entry: the next request slot exists. -/
def ReqRoom : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => WorldOK s ∧ memW s (globN s "bo" + 64) < 8

/-- A read-only callee keeps every guard that ignores locals and the clock (proved). -/
theorem ReadOnlyFn.keepsOn {W : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hW : LocalsFree W) (hG : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), W s → GuestInv s)
    {fname : MlS} (h : ReadOnlyFn fname) : KeepsOn W W fname := by
  obtain ⟨params, body, ret, hlook, hb⟩ := h
  refine ⟨params, body, ret, hlook, fun s hc hWs hnt hr => ?_⟩
  rw [hb s hc (hG s hWs) hnt hr]
  exact hW s _ _ hWs

theorem worldOK_guestInv {F : Type} (s : PanSemStateFiniteExact 64 F) (h : WorldOK s) :
    GuestInv s := h.1.1

theorem evmInv_guestInv {F : Type} (s : PanSemStateFiniteExact 64 F) (h : EvmInv s) :
    GuestInv s := h.1.1

/-- `EvmInv` implies `WorldOK` (the frame-level guard is stronger). -/
theorem worldOK_of_evmInv {F : Type} (s : PanSemStateFiniteExact 64 F) (h : EvmInv s) :
    WorldOK s :=
  ⟨h.1, h.2.elim fun S hS => ⟨S, hS.1⟩⟩

theorem localsOnly_txReady : LocalsOnly ["index"] TxReady := by
  intro F s locals k hl hP
  have ht := locN_congr s locals k "index" (hl "index" (by simp))
  refine ⟨localsFree_worldOK s locals k hP.1, ?_⟩
  show locN { s with locals := locals, clock := k } "index" < memW s (globN s "bo" + 80)
  rw [ht]; exact hP.2

theorem localsFree_reqsFresh : LocalsFree ReqsFresh :=
  fun s locals k h => ⟨localsFree_worldOK s locals k h.1, h.2⟩

/-! ### Outcome triples (proved rules, used to prove the frame glue)

`Hoare P prog Q`: every non-timeout run of `prog` from a `P` state ends with result `r` in a state
`t` such that `Q r t`. Relational facts are carried by ghost numbers inside `P`/`Q`. -/

structure Hoare (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop) (prog : ProgHOL 64)
    (Q : ∀ {F : Type}, Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop) :
    Prop where
  run : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → P s →
    (evaluateHOLFiniteState s prog).1 ≠ some .timeOut →
    Q (evaluateHOLFiniteState s prog).1 (evaluateHOLFiniteState s prog).2

section HoareRules

variable {P P' R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
  {Q : ∀ {F : Type}, Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop}

theorem Hoare.of_false {prog : ProgHOL 64}
    (h : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → False) : Hoare P prog Q :=
  ⟨fun s _ hP _ => (h s hP).elim⟩

theorem Hoare.mono {prog : ProgHOL 64} (h : Hoare P' prog Q)
    (hPP : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → P' s) : Hoare P prog Q :=
  ⟨fun s hcode hP hnt => h.run s hcode (hPP s hP) hnt⟩

theorem Hoare.skip
    (h : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → Q none s) :
    Hoare P .skip Q := by
  refine ⟨fun {F} s _ hP _ => ?_⟩
  rw [evaluateHOLFiniteState_skip]
  exact h s hP

theorem Hoare.seq {first second : ProgHOL 64}
    (h1 : Hoare P first fun r t => (r = none → R t) ∧ (r ≠ none → Q r t))
    (h2 : Hoare R second Q) : Hoare P (.seq first second) Q := by
  refine ⟨fun {F} s hcode hP hnt => ?_⟩
  have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata s first).1
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rcases hr : evaluateHOLFiniteState s first with ⟨r1, m⟩
  simp only [hr] at hnt hmeta ⊢
  change m.code = s.code at hmeta
  cases r1 with
  | none =>
    have h := h1.run s hcode hP (by rw [hr]; simp)
    rw [hr] at h
    exact h2.run m (hmeta.trans hcode) (h.1 rfl) hnt
  | some r =>
    have h := h1.run s hcode hP (by rw [hr]; exact hnt)
    rw [hr] at h
    exact h.2 (by simp)

theorem Hoare.ite {cond : ExpHOL 64} {yes no : ProgHOL 64}
    (hyes : Hoare (fun s => P s ∧ CondTrue cond s) yes Q)
    (hno : Hoare (fun s => P s ∧ CondFalse cond s) no Q)
    (herr : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → Q (some .error) s) :
    Hoare P (.ite cond yes no) Q := by
  refine ⟨fun {F} s hcode hP hnt => ?_⟩
  rw [evaluateHOLFiniteState_ite] at hnt ⊢
  revert hnt
  split <;> intro hnt
  · rename_i w hw
    revert hnt
    split <;> intro hnt
    · rename_i hz
      subst hz
      exact hno.run s hcode ⟨hP, hw⟩ hnt
    · rename_i hz
      exact hyes.run s hcode ⟨hP, w, hw, hz⟩ hnt
  · exact herr s hP

theorem resVarEq_lookup_ne (m : HolFiniteMapExact MlS (ValueHOL 64)) (name n : MlS)
    (o : Option (ValueHOL 64)) (h : n ≠ name) :
    (HolFiniteMapExact.resVarEq m (name, o)).lookup n = m.lookup n := by
  rcases o with _ | v
  · simp [HolFiniteMapExact.resVarEq, HolFiniteMapExact.eraseEq, FDOMSUB_HOL, h]
  · simp only [HolFiniteMapExact.resVarEq, HolFiniteMapExact.updateEq, FUPDATE_HOL]
    split
    · rename_i heq; exact absurd heq h
    · rfl

/-- `Q` does not read the locals outside `names`. -/
def PostLocalsOnly (names : List String)
    (Q : ∀ {F : Type}, Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop) :
    Prop :=
  ∀ {F : Type} (r : Option (PanSemResultExact 64)) (t : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)),
    (∀ n ∈ names, locals.lookup (ofString n) = t.locals.lookup (ofString n)) →
    Q r t → Q r { t with locals := locals }

theorem Hoare.dec {names : List String} {name : MlS} {shape : ShapeHOL} {init : ExpHOL 64}
    {body : ProgHOL 64} (hname : ∀ n ∈ names, ofString n ≠ name)
    (hinit : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64), P s →
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) init =
        some v → P' (setVarHOLFinite name v s))
    (hbody : Hoare P' body Q) (hQ : PostLocalsOnly names Q)
    (herr : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → Q (some .error) s) :
    Hoare P (.dec name shape init body) Q := by
  refine ⟨fun {F} s hcode hP hnt => ?_⟩
  rw [evaluateHOLFiniteState_dec_total] at hnt ⊢
  dsimp only at hnt ⊢
  revert hnt
  split <;> intro hnt
  · exact herr s hP
  · rename_i v hv
    revert hnt
    split <;> intro hnt
    · have hb := hbody.run (setVarHOLFinite name v s) hcode (hinit s v hP hv) hnt
      exact hQ _ _ _ (fun n hn => resVarEq_lookup_ne _ _ _ _ (hname n hn)) hb
    · exact herr s hP

theorem Hoare.assign {kind : VarKind} {name : MlS} {source : ExpHOL 64}
    (h : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64), P s →
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) source =
        some v → Q none (setKvarHOLFinite kind name v s))
    (herr : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → Q (some .error) s) :
    Hoare P (.assign kind name source) Q := by
  refine ⟨fun {F} s hcode hP hnt => ?_⟩
  rw [evaluateHOLFiniteState_assign] at hnt ⊢
  revert hnt
  split <;> intro hnt
  · exact herr s hP
  · rename_i v hv
    revert hnt
    split <;> intro hnt
    · exact h s v hP hv
    · exact herr s hP

/-- The installed body of a `FunSpec` function, at a successful lookup. -/
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
  subst hsame
  exact hspec _ hcode hPc hnt

/-- Handler-free call with no destination, callee described by a `FunSpec`. Results other than
a normal return are covered by `hother` (a call never yields `continue`). -/
theorem Hoare.call0 {Pc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Qc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop} {fname : MlS} {arguments : List (ExpHOL 64)}
    (hf : FunSpec Pc Qc fname) (hentry : CallEntryOn P Pc fname arguments)
    (hret : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F)
      (callee : HolFiniteMapExact MlS (ValueHOL 64)) (post : PanSemStateFiniteExact 64 F)
      (v : ValueHOL 64), s.code = originalRuntimeCode → P s →
      Qc (callEntryStateHOLFinite s callee) (some (.returned v)) post →
      Q none { post with locals := s.locals })
    (hother : ∀ {F : Type} (r : Option (PanSemResultExact 64)) (t : PanSemStateFiniteExact 64 F),
      r ≠ none → r ≠ some .continue → Q r t) :
    Hoare P (.call (some (none, none)) fname arguments) Q := by
  refine ⟨fun {F} s hcode hP hnt => ?_⟩
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  rcases hargs : evalListHOLFinite s
      (h := fun address => Classical.propDecidable (s.memaddrs address)) arguments with
    _ | values
  · exact hother _ _ (by simp) (by simp)
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · exact hother _ _ (by simp) (by simp)
    · simp only [hl] at hnt ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
        have hPc := hentry s values body' callee ret' hcode hP hargs hl
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with
          ⟨res, post⟩
        simp only [hrun] at hnt ⊢
        have hQc (hsafe : res ≠ some .timeOut) : Qc (callEntryStateHOLFinite s callee) res post := by
          have := FunSpec.at_lookup hf s hcode values body' callee ret' hl hPc (by rw [hrun]; exact hsafe)
          rw [hrun] at this
          exact this
        cases res with
        | none => exact hother _ _ (by simp) (by simp)
        | some r =>
          cases r with
          | returned v =>
            dsimp only
            split
            · exact hret s callee post v hcode hP (hQc (by simp))
            · exact hother _ _ (by simp) (by simp)
          | timeOut => simp at hnt
          | _ => exact hother _ _ (by simp) (by simp)

/-- Call with an exception handler and no destination: the handler runs on
`setVar var v {post with locals := caller locals}` after the callee raised `exn`. -/
theorem Hoare.callH {Pc Ph : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Qc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop} {fname : MlS} {arguments : List (ExpHOL 64)}
    {exn var : MlS} {handler : ProgHOL 64}
    (hf : FunSpec Pc Qc fname) (hentry : CallEntryOn P Pc fname arguments)
    (hret : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F)
      (callee : HolFiniteMapExact MlS (ValueHOL 64)) (post : PanSemStateFiniteExact 64 F)
      (v : ValueHOL 64), s.code = originalRuntimeCode → P s →
      Qc (callEntryStateHOLFinite s callee) (some (.returned v)) post →
      Q none { post with locals := s.locals })
    (hexn : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F)
      (callee : HolFiniteMapExact MlS (ValueHOL 64)) (post : PanSemStateFiniteExact 64 F)
      (v : ValueHOL 64), s.code = originalRuntimeCode → P s →
      Qc (callEntryStateHOLFinite s callee) (some (.exception exn v)) post →
      Ph (setVarHOLFinite var v { post with locals := s.locals }))
    (hh : Hoare Ph handler Q)
    (hother : ∀ {F : Type} (r : Option (PanSemResultExact 64)) (t : PanSemStateFiniteExact 64 F),
      r ≠ none → r ≠ some .continue → Q r t) :
    Hoare P (.call (some (none, some (exn, var, handler))) fname arguments) Q := by
  refine ⟨fun {F} s hcode hP hnt => ?_⟩
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  rcases hargs : evalListHOLFinite s
      (h := fun address => Classical.propDecidable (s.memaddrs address)) arguments with
    _ | values
  · exact hother _ _ (by simp) (by simp)
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · exact hother _ _ (by simp) (by simp)
    · simp only [hl] at hnt ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
        have hPc := hentry s values body' callee ret' hcode hP hargs hl
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata
          (callEntryStateHOLFinite s callee) body').1
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with
          ⟨res, post⟩
        simp only [hrun] at hnt hmeta ⊢
        change post.code = s.code at hmeta
        have hQc (hsafe : res ≠ some .timeOut) : Qc (callEntryStateHOLFinite s callee) res post := by
          have := FunSpec.at_lookup hf s hcode values body' callee ret' hl hPc (by rw [hrun]; exact hsafe)
          rw [hrun] at this
          exact this
        cases res with
        | none => exact hother _ _ (by simp) (by simp)
        | some r =>
          cases r with
          | returned v =>
            dsimp only
            split
            · exact hret s callee post v hcode hP (hQc (by simp))
            · exact hother _ _ (by simp) (by simp)
          | timeOut => simp at hnt
          | exception eid v =>
            dsimp only at hnt ⊢
            by_cases hid : eid = exn
            · subst hid
              simp only [↓reduceIte] at hnt ⊢
              rcases hsh : s.eshapes.lookup eid with _ | shape
              · exact hother _ _ (by simp) (by simp)
              · simp only [hsh] at hnt ⊢
                by_cases hv : (shapeEqHOL (shapeOfHOLExact v) shape &&
                    isValidValueHOLExact s.toExact .local var v) = true
                · simp only [hv, ↓reduceIte] at hnt ⊢
                  exact hh.run _ (by simp [setVarHOLFinite]; exact hmeta.trans hcode)
                    (hexn s callee post v hcode hP (hQc (by simp))) hnt
                · simp only [hv, Bool.false_eq_true, ↓reduceIte]
                  exact hother _ _ (by simp) (by simp)
            · simp only [hid, ↓reduceIte]
              exact hother _ _ (by simp) (by simp)
          | _ => exact hother _ _ (by simp) (by simp)

end HoareRules

/-! ### Evaluating the `run_frames` loop tests -/

/-- Evaluation of an expression at a state (the decider every rewrite lemma uses). -/
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

theorem evalAt_const {F : Type} (t : PanSemStateFiniteExact 64 F) (k : BitVec 64)
    (v : ValueHOL 64) (h : evalAt t (.const k) = some v) : v = .val (.word k) := by
  simp only [evalAt, evalHOLExact] at h
  cases h; rfl

theorem evalAt_local {F : Type} (t : PanSemStateFiniteExact 64 F) (n : String) (a : BitVec 64)
    (h : evalAt t (.var .local (ofString n)) = some (.val (.word a))) : a.toNat = locN t n := by
  simp only [evalAt, evalHOLExact] at h
  simp [locN] at h ⊢
  rw [h]

theorem evalAt_loadG' {F : Type} (t : PanSemStateFiniteExact 64 F) (g : String) (k a : BitVec 64)
    (h : evalAt t (.load .one (.op .add [.var .global (ofString g), .const k])) =
      some (.val (.word a))) :
    a.toNat = memW t (globN t g + k.toNat) := by
  simp [evalAt, evalHOLExact, evalListHOLExact] at h
  rcases hg : t.globals.lookup (ofString g) with _ | v
  · simp [hg] at h
  · rcases v with x | fs | ⟨nm, fs⟩
    · cases x with
      | word x =>
        simp [hg, valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact] at h
        have hadd : BitVec.ofNat 64 (x.toNat + k.toNat) = x + k := by
          rw [BitVec.add_def]
        simp only [globN, memW, hg, hadd, h.2]
    · simp [hg, valueIsWord] at h
    · simp [hg, valueIsWord] at h

/-- A one-word load from `global + k` that succeeds yields the word `memW t (globN t g + k)`. -/
theorem evalAt_loadG {F : Type} (t : PanSemStateFiniteExact 64 F) (g : String) (k : BitVec 64)
    (v : ValueHOL 64)
    (h : evalAt t (.load .one (.op .add [.var .global (ofString g), .const k])) = some v) :
    ∃ a : BitVec 64, v = .val (.word a) ∧ a.toNat = memW t (globN t g + k.toNat) := by
  have hv : ∃ a : BitVec 64, v = .val (.word a) := by
    simp [evalAt, evalHOLExact, evalListHOLExact] at h
    rcases hg : t.globals.lookup (ofString g) with _ | w
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
  exact ⟨a, rfl, evalAt_loadG' t g k a h⟩

theorem locN_setVar_same {F : Type} (t : PanSemStateFiniteExact 64 F) (n : String)
    (w : BitVec 64) : locN (setVarHOLFinite (ofString n) (.val (.word w)) t) n = w.toNat := by
  simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]

theorem locN_setVar_ne {F : Type} (t : PanSemStateFiniteExact 64 F) (n : String) (m : MlS)
    (v : ValueHOL 64) (h : ofString n ≠ m) : locN (setVarHOLFinite m v t) n = locN t n := by
  have hl : (t.locals.update (m, v)).lookup (ofString n) = t.locals.lookup (ofString n) := by
    simp [HolFiniteMapExact.update, FUPDATE, Ne.symm h]
  simp only [locN, setVarHOLFinite, hl]

/-! ### The EVM potential reads only memory and globals -/

def evmFp {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  2 * (evmChain s).length + (if EvmDone s then 0 else 1)

def evmS {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  ((evmChain s).map fun ec => memW s (ec.1 + 72)).sum

theorem evmPot_eq {F : Type} (s : PanSemStateFiniteExact 64 F) :
    evmPot s = evmR s * (evmPotF * evmPotS) + evmFp s * evmPotS + evmS s := rfl

theorem memW_congr {F : Type} {s t : PanSemStateFiniteExact 64 F} (h : t.memory = s.memory) :
    memW t = memW s := by
  funext a; simp [memW, h]

theorem globN_congr {F : Type} {s t : PanSemStateFiniteExact 64 F} (h : t.globals = s.globals) :
    globN t = globN s := by
  funext a; simp [globN, h]

theorem evmChainFrom_congr {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (h : t.memory = s.memory) :
    ∀ (fuel e c : Nat), evmChainFrom t fuel e c = evmChainFrom s fuel e c
  | 0, _, _ => rfl
  | fuel + 1, e, c => by
    simp only [evmChainFrom, memW_congr h, evmChainFrom_congr h fuel]

theorem evmChain_congr {F : Type} {s t : PanSemStateFiniteExact 64 F} (hm : t.memory = s.memory)
    (hg : t.globals = s.globals) : evmChain t = evmChain s := by
  simp only [evmChain, evmChainFrom_congr hm, globN_congr hg]

theorem evmDone_congr {F : Type} {s t : PanSemStateFiniteExact 64 F} (hm : t.memory = s.memory)
    (hg : t.globals = s.globals) : EvmDone t ↔ EvmDone s := by
  simp only [EvmDone, memW_congr hm, globN_congr hg]

theorem evm_congr {F : Type} {s t : PanSemStateFiniteExact 64 F} (hm : t.memory = s.memory)
    (hg : t.globals = s.globals) :
    evmPot t = evmPot s ∧ evmR t = evmR s ∧ (evmChain t).length = (evmChain s).length ∧
      evmFp t = evmFp s := by
  have hc := evmChain_congr hm hg
  have hd := evmDone_congr hm hg
  refine ⟨?_, ?_, by rw [hc], ?_⟩
  · simp only [evmPot, hc, memW_congr hm, hd]
  · simp only [evmR, hc, memW_congr hm]
  · simp only [evmFp, hc, hd]

theorem memW_lt {F : Type} (s : PanSemStateFiniteExact 64 F) (a : Nat) : memW s a < 2 ^ 64 := by
  unfold memW
  split
  rename_i w _
  exact w.isLt

theorem sum_map_memW_le {F : Type} (s : PanSemStateFiniteExact 64 F) (off : Nat) :
    ∀ l : List Ivl, (l.map fun ec => memW s (ec.1 + off)).sum ≤ l.length * (2 ^ 64 - 1)
  | [] => by simp
  | x :: xs => by
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    have h1 := memW_lt s (x.1 + off)
    have h2 := sum_map_memW_le s off xs
    omega

theorem evmInv_len {F : Type} (s : PanSemStateFiniteExact 64 F) (h : EvmInv s) :
    (evmChain s).length ≤ maxChain := by
  obtain ⟨_, S, hS⟩ := h
  exact hS.2.2.1

theorem evmS_lt {F : Type} (s : PanSemStateFiniteExact 64 F) (h : EvmInv s) : evmS s < evmPotS := by
  have hlen := evmInv_len s h
  have hle := sum_map_memW_le s 72 (evmChain s)
  have hm : (evmChain s).length * (2 ^ 64 - 1) < maxChain * 2 ^ 64 := by
    have : (evmChain s).length * (2 ^ 64 - 1) ≤ maxChain * (2 ^ 64 - 1) :=
      Nat.mul_le_mul_right _ hlen
    simp only [maxChain] at this ⊢
    omega
  show ((evmChain s).map fun ec => memW s (ec.1 + 72)).sum < maxChain * 2 ^ 64
  omega

theorem evmFp_lt {F : Type} (s : PanSemStateFiniteExact 64 F) (h : EvmInv s) :
    evmFp s < evmPotF := by
  have hlen := evmInv_len s h
  unfold evmFp evmPotF
  simp only [maxChain] at hlen ⊢
  split <;> omega

/-- The decrease argument of `run_frames`: under `EvmInv`, `R` not larger and `F` strictly
smaller is below any potential with those `R`, `F` components. -/
theorem evmPot_lt_bound {F : Type} (t : PanSemStateFiniteExact 64 F) (h : EvmInv t) {R0 F0 : Nat}
    (hR : evmR t ≤ R0) (hF : evmFp t < F0) :
    evmPot t < R0 * (evmPotF * evmPotS) + F0 * evmPotS := by
  have hS := evmS_lt t h
  have hFp := evmFp_lt t h
  rw [evmPot_eq]
  rcases Nat.lt_or_ge (evmR t) R0 with hlt | hge
  · have h1 : evmFp t * evmPotS + evmS t < evmPotF * evmPotS := by
      have : (evmFp t + 1) * evmPotS ≤ evmPotF * evmPotS := Nat.mul_le_mul_right _ hFp
      rw [Nat.add_mul, Nat.one_mul] at this
      omega
    have h2 : (evmR t + 1) * (evmPotF * evmPotS) ≤ R0 * (evmPotF * evmPotS) :=
      Nat.mul_le_mul_right _ hlt
    rw [Nat.add_mul, Nat.one_mul] at h2
    have h3 : 0 ≤ F0 * evmPotS := Nat.zero_le _
    omega
  · have hReq : evmR t = R0 := le_antisymm hR hge
    have h2 : (evmFp t + 1) * evmPotS ≤ F0 * evmPotS := Nat.mul_le_mul_right _ hF
    rw [Nat.add_mul, Nat.one_mul] at h2
    rw [hReq]
    omega

theorem evmPot_ge {F : Type} (s : PanSemStateFiniteExact 64 F) :
    evmR s * (evmPotF * evmPotS) + evmFp s * evmPotS ≤ evmPot s := by
  rw [evmPot_eq]; omega

/-! ### Loop tests of `run_frames` -/

theorem cond_loadG {F : Type} (t : PanSemStateFiniteExact 64 F) (op : Cmp) (g : String)
    (k w : BitVec 64)
    (h : evalAt t (.cmp op (.load .one (.op .add [.var .global (ofString g), .const k]))
      (.const 0)) = some (.val (.word w))) :
    ∃ a : BitVec 64, a.toNat = memW t (globN t g + k.toNat) ∧
      w = if Flapjack.Compiler.Encoders.Asm.wordCmpHOL op a 0 then 1 else 0 := by
  obtain ⟨a, b, ha, hb, rfl⟩ := evalAt_cmp t op _ _ w h
  obtain ⟨a', ha', hm⟩ := evalAt_loadG t g k _ ha
  cases ha'
  have hb' := evalAt_const t 0 _ hb
  cases hb'
  exact ⟨a, hm, rfl⟩

theorem condTrue_ne0 {F : Type} {t : PanSemStateFiniteExact 64 F} {g : String} {k : BitVec 64}
    (h : CondTrue (.cmp .notEqual (.load .one (.op .add [.var .global (ofString g), .const k]))
      (.const 0)) t) : memW t (globN t g + k.toNat) ≠ 0 := by
  obtain ⟨w, hw, hne⟩ := h
  obtain ⟨a, ha, rfl⟩ := cond_loadG t _ g k w hw
  rw [← ha]
  intro h0
  apply hne
  have : a = 0 := BitVec.eq_of_toNat_eq (by simpa using h0)
  subst this
  simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

theorem condFalse_ne0 {F : Type} {t : PanSemStateFiniteExact 64 F} {g : String} {k : BitVec 64}
    (h : CondFalse (.cmp .notEqual (.load .one (.op .add [.var .global (ofString g), .const k]))
      (.const 0)) t) : memW t (globN t g + k.toNat) = 0 := by
  obtain ⟨a, ha, h0⟩ := cond_loadG t _ g k 0 h
  rw [← ha]
  by_cases hz : a = 0
  · subst hz; rfl
  · exfalso
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at h0
    exact hz h0

theorem condTrue_eq0 {F : Type} {t : PanSemStateFiniteExact 64 F} {g : String} {k : BitVec 64}
    (h : CondTrue (.cmp .equal (.load .one (.op .add [.var .global (ofString g), .const k]))
      (.const 0)) t) : memW t (globN t g + k.toNat) = 0 := by
  obtain ⟨w, hw, hne⟩ := h
  obtain ⟨a, ha, rfl⟩ := cond_loadG t _ g k w hw
  rw [← ha]
  by_cases hz : a = 0
  · subst hz; rfl
  · exfalso; apply hne
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    exact hz

theorem condFalse_eq0 {F : Type} {t : PanSemStateFiniteExact 64 F} {g : String} {k : BitVec 64}
    (h : CondFalse (.cmp .equal (.load .one (.op .add [.var .global (ofString g), .const k]))
      (.const 0)) t) : memW t (globN t g + k.toNat) ≠ 0 := by
  obtain ⟨a, ha, h0⟩ := cond_loadG t _ g k 0 h
  rw [← ha]
  intro hz
  have : a = 0 := BitVec.eq_of_toNat_eq (by simpa using hz)
  subst this
  simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at h0

theorem cond_local {F : Type} (t : PanSemStateFiniteExact 64 F) (op : Cmp) (n : String)
    (r : ExpHOL 64) (w : BitVec 64)
    (h : evalAt t (.cmp op (.var .local (ofString n)) r) = some (.val (.word w))) :
    ∃ a b : BitVec 64, a.toNat = locN t n ∧ evalAt t r = some (.val (.word b)) ∧
      w = if Flapjack.Compiler.Encoders.Asm.wordCmpHOL op a b then 1 else 0 := by
  obtain ⟨a, b, ha, hb, rfl⟩ := evalAt_cmp t op _ _ w h
  exact ⟨a, b, evalAt_local t n a ha, hb, rfl⟩

theorem condTrue_local_ne0 {F : Type} {t : PanSemStateFiniteExact 64 F} {n : String}
    (h : CondTrue (.cmp .notEqual (.var .local (ofString n)) (.const 0)) t) : locN t n ≠ 0 := by
  obtain ⟨w, hw, hne⟩ := h
  obtain ⟨a, b, ha, hb, rfl⟩ := cond_local t _ n _ w hw
  cases evalAt_const t 0 _ hb
  rw [← ha]
  intro h0
  apply hne
  have : a = 0 := BitVec.eq_of_toNat_eq (by simpa using h0)
  subst this
  simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

theorem condFalse_local_ne0 {F : Type} {t : PanSemStateFiniteExact 64 F} {n : String}
    (h : CondFalse (.cmp .notEqual (.var .local (ofString n)) (.const 0)) t) : locN t n = 0 := by
  obtain ⟨a, b, ha, hb, h0⟩ := cond_local t _ n _ 0 h
  cases evalAt_const t 0 _ hb
  rw [← ha]
  by_cases hz : a = 0
  · subst hz; rfl
  · exfalso
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at h0
    exact hz h0

theorem cond_notLower {F : Type} {t : PanSemStateFiniteExact 64 F} {n g : String} {k w : BitVec 64}
    (h : evalAt t (.cmp .notLower (.var .local (ofString n))
      (.load .one (.op .add [.var .global (ofString g), .const k]))) = some (.val (.word w))) :
    (w ≠ 0 → memW t (globN t g + k.toNat) ≤ locN t n) ∧
      (w = 0 → locN t n < memW t (globN t g + k.toNat)) := by
  obtain ⟨a, b, ha, hb, rfl⟩ := cond_local t _ n _ w h
  obtain ⟨b', hb', hm⟩ := evalAt_loadG t g k _ hb
  cases hb'
  rw [← ha, ← hm]
  constructor
  · intro hw
    by_cases hlt : a < b
    · exfalso; apply hw; simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlt]
    · exact Nat.le_of_not_lt (fun hc => hlt (BitVec.lt_def.mpr hc))
  · intro hw
    by_cases hlt : a < b
    · exact BitVec.lt_def.mp hlt
    · exfalso; simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlt] at hw

/-! ### The glue, proved -/

section RunFramesGlue

variable (p0 R0 L0 F0 : Nat)

/-- Loop-head facts carried through the body: the potential components of the head. -/
def GPre : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun t => EvmInv t ∧ evmPot t = p0 ∧ evmR t = R0 ∧ (evmChain t).length = L0 ∧ evmFp t = F0

def GQ : ∀ {F : Type}, Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop :=
  fun r t => (r = none ∨ r = some .continue) → (EvmInv t ∧ evmPot t < p0) ∨ locN t "go" = 0

def GMid : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun t => (GPre p0 R0 L0 F0 t ∧ EvmDone t ∧ locN t "done" ≠ 0) ∨
    (EvmInv t ∧ evmPot t < p0 ∧ locN t "done" = 0)

def GA : ∀ {F : Type}, Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop :=
  fun r t => (r = none → GMid p0 R0 L0 F0 t) ∧ (r ≠ none → GQ p0 r t)

theorem gq_other {F : Type} (r : Option (PanSemResultExact 64)) (t : PanSemStateFiniteExact 64 F)
    (h1 : r ≠ none) (h2 : r ≠ some .continue) : GQ p0 r t := by
  intro h; rcases h with h | h <;> contradiction

theorem ga_other {F : Type} (r : Option (PanSemResultExact 64)) (t : PanSemStateFiniteExact 64 F)
    (h1 : r ≠ none) (h2 : r ≠ some .continue) : GA p0 R0 L0 F0 r t :=
  ⟨fun h => absurd h h1, fun _ => gq_other p0 r t h1 h2⟩

theorem gpre_congr {F : Type} {t u : PanSemStateFiniteExact 64 F} (hm : u.memory = t.memory)
    (hg : u.globals = t.globals) (hinv : EvmInv u) (h : GPre p0 R0 L0 F0 t) :
    GPre p0 R0 L0 F0 u := by
  obtain ⟨_, h1, h2, h3, h4⟩ := h
  obtain ⟨e1, e2, e3, e4⟩ := evm_congr hm hg
  exact ⟨hinv, e1.trans h1, e2.trans h2, e3.trans h3, e4.trans h4⟩

theorem evmInv_locals {F : Type} {t : PanSemStateFiniteExact 64 F}
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (h : EvmInv t) :
    EvmInv { t with locals := locals } :=
  localsFree_evmInv t locals t.clock h

theorem evmInv_setVar {F : Type} {t : PanSemStateFiniteExact 64 F} (n : MlS) (v : ValueHOL 64)
    (h : EvmInv t) : EvmInv (setVarHOLFinite n v t) :=
  localsFree_evmInv t _ t.clock h

theorem evmInv_entry {F : Type} {t : PanSemStateFiniteExact 64 F}
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (h : EvmInv t) :
    EvmInv (callEntryStateHOLFinite t callee) :=
  localsFree_evmInv t _ _ h

theorem gq_postLocals : PostLocalsOnly ["go"] (GQ p0) := by
  intro F r t locals hl h hr
  rcases h hr with ⟨hi, hp⟩ | hgo
  · left
    exact ⟨evmInv_locals locals hi, by rw [(evm_congr (s := t) (t := { t with locals := locals }) rfl rfl).1]; exact hp⟩
  · right
    rw [locN_congr t locals t.clock "go" (hl "go" (by simp))]
    exact hgo

theorem ga_postLocals : PostLocalsOnly ["go", "done"] (GA p0 R0 L0 F0) := by
  intro F r t locals hl h
  have hgo := hl "go" (by simp)
  have hdone := locN_congr t locals t.clock "done" (hl "done" (by simp))
  refine ⟨fun hr => ?_, fun hr => gq_postLocals p0 r t locals (fun n hn => by
    simp at hn; subst hn; exact hgo) (h.2 hr)⟩
  rcases h.1 hr with ⟨hp, hd, hn⟩ | ⟨hi, hp, hn⟩
  · left
    refine ⟨gpre_congr p0 R0 L0 F0 (t := t) (u := { t with locals := locals }) rfl rfl
      (evmInv_locals locals hp.1) hp, ?_, ?_⟩
    · exact (evmDone_congr (s := t) (t := { t with locals := locals }) rfl rfl).2 hd
    · change locN { t with locals := locals, clock := t.clock } "done" ≠ 0
      rw [hdone]; exact hn
  · right
    refine ⟨evmInv_locals locals hi, ?_, ?_⟩
    · rw [(evm_congr (s := t) (t := { t with locals := locals }) rfl rfl).1]; exact hp
    · change locN { t with locals := locals, clock := t.clock } "done" = 0
      rw [hdone]; exact hn

end RunFramesGlue

/-- `run_frames` is the 585th declaration of the AST. -/
theorem lookup_run_frames :
    originalRuntimeCode.lookup (ofString "run_frames") =
      some ((sourceFunctionEntry Guest.Software.guestFn_run_frames).2) := by
  exact originalRuntimeCode_lookup_of_guestAst_getElem 584 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_run_frames) rfl

section RunFramesGlue2

variable (p0 R0 L0 F0 : Nat)

/-- After `dec done 0`. -/
def GP1 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun t => GPre p0 R0 L0 F0 t ∧ locN t "done" = 0

/-- After `dec pc (load ev)` on the not-yet-done path. -/
def GPpc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun t => GPre p0 R0 L0 F0 t ∧ locN t "done" = 0 ∧
    memW t (globN t "cur_cont" + 32) = 0 ∧ memW t (globN t "ev" + 104) ≠ 0 ∧
    locN t "pc" = memW t (globN t "ev")

/-- At the `op_dispatch` call: a running frame. -/
def GPdisp : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun t => GPre p0 R0 L0 F0 t ∧ locN t "done" = 0 ∧ ¬ EvmDone t ∧ F0 = 2 * L0 + 1

/-- In the `EvmErr` handler of `op_dispatch`. -/
def GPh : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun t => EvmInv t ∧ (evmChain t).length = L0 ∧ evmR t ≤ R0 ∧ locN t "done" = 0 ∧
    F0 = 2 * L0 + 1

/-- The done branch, before `frame_epilogue`. -/
def GPdone : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun t => GPre p0 R0 L0 F0 t ∧ EvmDone t

/-- After `frame_epilogue`. -/
def GPepi : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun t => EvmInv t ∧ EvmDone t ∧ (evmChain t).length = L0 ∧ evmR t ≤ R0 ∧ 2 * L0 ≤ F0

/-- At the `finish_child` call. -/
def GPfin : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun t => GPepi R0 L0 F0 t ∧ memW t (globN t "cur_cont" + 16) ≠ 0

/-- In the `EvmErr` handler of `finish_child`. -/
def GPh4 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun t => EvmInv t ∧ (evmChain t).length + 1 = L0 ∧ evmR t ≤ R0 ∧ 2 * L0 ≤ F0

end RunFramesGlue2

theorem evmFp_done {F : Type} {t : PanSemStateFiniteExact 64 F} (h : EvmDone t) :
    evmFp t = 2 * (evmChain t).length := by
  simp [evmFp, h]

theorem evmFp_notDone {F : Type} {t : PanSemStateFiniteExact 64 F} (h : ¬ EvmDone t) :
    evmFp t = 2 * (evmChain t).length + 1 := by
  simp [evmFp, h]

theorem evmFp_le {F : Type} (t : PanSemStateFiniteExact 64 F) :
    evmFp t ≤ 2 * (evmChain t).length + 1 := by
  unfold evmFp; split <;> omega


set_option maxHeartbeats 4000000 in
/-- Glue (round-2 Astra item 6: now PROVED): the four frame contracts compose to
`run_frames_step`. The loop body is evaluated symbolically with the `Hoare` rules: a running frame
dispatches one instruction (`evmPot` drops, or `EvmErr` → `frame_exception` halts the frame:
`F` drops by one); a done frame runs `frame_epilogue` and then either leaves the loop
(`go := 0`, outermost frame) or pops the child (`finish_child`, then possibly
`frame_exception`: the chain is one shorter, so `F` drops). -/
theorem run_frames_step_of_specs
    (h1 : FunSpec (fun s => EvmInv s ∧ ¬ EvmDone s)
      (fun s r post =>
        ((∃ v, r = some (.returned v)) → EvmInv post ∧ evmPot post < evmPot s) ∧
        (IsEvmErr r → EvmInv post ∧ (evmChain post).length = (evmChain s).length ∧
          evmR post ≤ evmR s))
      (ofString "op_dispatch"))
    (h2 : FunSpec EvmInv
      (OnReturn fun s post => EvmInv post ∧ EvmDone post ∧
        (evmChain post).length = (evmChain s).length ∧ evmR post ≤ evmR s)
      (ofString "frame_exception"))
    (h3 : FunSpec (fun s => EvmInv s ∧ EvmDone s)
      (OnReturn fun s post => EvmInv post ∧ EvmDone post ∧
        (evmChain post).length = (evmChain s).length ∧ evmR post ≤ evmR s)
      (ofString "frame_epilogue"))
    (h4 : FunSpec (fun s => EvmInv s ∧ EvmDone s ∧ memW s (globN s "cur_cont" + 16) ≠ 0)
      (fun s r post => ((∃ v, r = some (.returned v)) ∨ IsEvmErr r) →
        EvmInv post ∧ (evmChain post).length + 1 = (evmChain s).length ∧ evmR post ≤ evmR s)
      (ofString "finish_child")) :
    ∀ c b, runFramesLoop = some (c, b) →
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → EvmInv s →
      LoopActive c s →
      ((evaluateHOLFiniteState (decClockHOLFinite s) b).1 = none ∨
        (evaluateHOLFiniteState (decClockHOLFinite s) b).1 = some .continue) →
      (EvmInv (evaluateHOLFiniteState (decClockHOLFinite s) b).2 ∧
        evmPot (evaluateHOLFiniteState (decClockHOLFinite s) b).2 < evmPot s) ∨
      locN (evaluateHOLFiniteState (decClockHOLFinite s) b).2 "go" = 0 := by
  intro c b hcb F s hcode hinv _hact hflow
  unfold runFramesLoop at hcb
  rw [lookup_run_frames] at hcb
  simp only [sourceFunctionEntry, Guest.Software.guestFn_run_frames,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.some.injEq, Prod.mk.injEq] at hcb
  obtain ⟨-, hb⟩ := hcb
  -- ghost values of the loop head
  set p0 := evmPot s with hp0
  set R0 := evmR s with hR0
  set L0 := (evmChain s).length with hL0
  set F0 := evmFp s with hF0
  have hfin : ∀ {F : Type} (t : PanSemStateFiniteExact 64 F), EvmInv t → evmR t ≤ R0 →
      evmFp t < F0 → evmPot t < p0 := fun t ht hR hF =>
    lt_of_lt_of_le (evmPot_lt_bound t ht hR hF) (evmPot_ge s)
  have key : Hoare (GPre p0 R0 L0 F0) b (GQ p0) := by
    subst hb
    refine Hoare.dec (names := ["go"]) (P' := GP1 p0 R0 L0 F0) (by decide) ?_ ?_
      (gq_postLocals p0) (fun _ _ => gq_other p0 _ _ (by simp) (by simp))
    · intro F t v hP hv
      cases evalAt_const t 0 v hv
      refine ⟨gpre_congr p0 R0 L0 F0 (t := t) (u := setVarHOLFinite _ _ t) rfl rfl
        (evmInv_setVar _ _ hP.1) hP, ?_⟩
      rw [locN_setVar_same]; rfl
    · refine Hoare.seq (R := GMid p0 R0 L0 F0) ?_ ?_
      · -- the tests and the instruction
        refine Hoare.ite ?_ ?_ (fun _ _ => ga_other p0 R0 L0 F0 _ _ (by simp) (by simp))
        · -- `cur_cont+32 ≠ 0`: done
          refine Hoare.assign (fun t v hP hv => ?_)
            (fun _ _ => ga_other p0 R0 L0 F0 _ _ (by simp) (by simp))
          cases evalAt_const t 1 v hv
          refine ⟨fun _ => Or.inl ⟨?_, ?_, ?_⟩, fun h => absurd rfl h⟩
          · exact gpre_congr p0 R0 L0 F0 (t := t) (u := setKvarHOLFinite .local _ _ t) rfl rfl
              (evmInv_setVar _ _ hP.1.1.1) hP.1.1
          · refine (evmDone_congr (s := t) (t := setKvarHOLFinite .local _ _ t) rfl rfl).2 ?_
            have := condTrue_ne0 hP.2
            exact Or.inl (by simpa using this)
          · show locN (setVarHOLFinite (ofString "done") (.val (.word 1)) t) "done" ≠ 0
            rw [locN_setVar_same]; decide
        · refine Hoare.ite ?_ ?_ (fun _ _ => ga_other p0 R0 L0 F0 _ _ (by simp) (by simp))
          · -- `ev+104 = 0`: done
            refine Hoare.assign (fun t v hP hv => ?_)
              (fun _ _ => ga_other p0 R0 L0 F0 _ _ (by simp) (by simp))
            cases evalAt_const t 1 v hv
            refine ⟨fun _ => Or.inl ⟨?_, ?_, ?_⟩, fun h => absurd rfl h⟩
            · exact gpre_congr p0 R0 L0 F0 (t := t) (u := setKvarHOLFinite .local _ _ t) rfl rfl
                (evmInv_setVar _ _ hP.1.1.1.1) hP.1.1.1
            · refine (evmDone_congr (s := t) (t := setKvarHOLFinite .local _ _ t) rfl rfl).2 ?_
              have := condTrue_eq0 hP.2
              exact Or.inr (Or.inl (by simpa using this))
            · show locN (setVarHOLFinite (ofString "done") (.val (.word 1)) t) "done" ≠ 0
              rw [locN_setVar_same]; decide
          · refine Hoare.dec (names := ["go", "done"]) (P' := GPpc p0 R0 L0 F0) (by decide) ?_ ?_
              (ga_postLocals p0 R0 L0 F0)
              (fun _ _ => ga_other p0 R0 L0 F0 _ _ (by simp) (by simp))
            · intro F t v hP hv
              obtain ⟨⟨hP1, hc1⟩, hc2⟩ := hP
              obtain ⟨a, rfl, ha⟩ := evalAt_loadG t "ev" 0 v hv
              refine ⟨gpre_congr p0 R0 L0 F0 (t := t) (u := setVarHOLFinite _ _ t) rfl rfl
                (evmInv_setVar _ _ hP1.1.1) hP1.1, ?_, ?_, ?_, ?_⟩
              · rw [locN_setVar_ne t "done" (ofString "pc") _ (by decide)]; exact hP1.2
              · show memW t (globN t "cur_cont" + 32) = 0
                have := condFalse_ne0 hc1
                simpa using this
              · show memW t (globN t "ev" + 104) ≠ 0
                have := condFalse_eq0 hc2
                simpa using this
              · rw [locN_setVar_same]
                show a.toNat = memW t (globN t "ev")
                simpa using ha
            · refine Hoare.ite ?_ ?_ (fun _ _ => ga_other p0 R0 L0 F0 _ _ (by simp) (by simp))
              · -- `pc ≥ code length`: done
                refine Hoare.assign (fun t v hP hv => ?_)
                  (fun _ _ => ga_other p0 R0 L0 F0 _ _ (by simp) (by simp))
                cases evalAt_const t 1 v hv
                obtain ⟨⟨hpre, _, _, _, hpc⟩, w, hw, hne⟩ := hP
                refine ⟨fun _ => Or.inl ⟨?_, ?_, ?_⟩, fun h => absurd rfl h⟩
                · exact gpre_congr p0 R0 L0 F0 (t := t) (u := setKvarHOLFinite .local _ _ t)
                    rfl rfl (evmInv_setVar _ _ hpre.1) hpre
                · refine (evmDone_congr (s := t) (t := setKvarHOLFinite .local _ _ t) rfl rfl).2 ?_
                  have := (cond_notLower hw).1 hne
                  refine Or.inr (Or.inr ?_)
                  rw [← hpc]
                  simpa using this
                · show locN (setVarHOLFinite (ofString "done") (.val (.word 1)) t) "done" ≠ 0
                  rw [locN_setVar_same]; decide
              · -- running frame: dispatch one instruction
                refine Hoare.dec (names := ["go", "done"]) (P' := GPdisp p0 R0 L0 F0) (by decide)
                  ?_ ?_ (ga_postLocals p0 R0 L0 F0)
                  (fun _ _ => ga_other p0 R0 L0 F0 _ _ (by simp) (by simp))
                · intro F t v hP hv
                  cases evalAt_const t 0 v hv
                  obtain ⟨⟨hpre, hdone, hc1, hc2, hpc⟩, hc3⟩ := hP
                  have hlt := (cond_notLower hc3).2 rfl
                  have hnd : ¬ EvmDone t := by
                    rintro (h | h | h)
                    · exact h hc1
                    · exact hc2 h
                    · rw [← hpc] at h
                      simp at hlt
                      omega
                  refine ⟨gpre_congr p0 R0 L0 F0 (t := t) (u := setVarHOLFinite _ _ t) rfl rfl
                    (evmInv_setVar _ _ hpre.1) hpre, ?_, ?_, ?_⟩
                  · rw [locN_setVar_ne t "done" (ofString "err") _ (by decide)]; exact hdone
                  · exact fun h => hnd ((evmDone_congr (s := t) (t := setVarHOLFinite _ _ t)
                      rfl rfl).1 h)
                  · rw [← hpre.2.2.2.2, ← hpre.2.2.2.1, evmFp_notDone hnd]
                · refine Hoare.callH (Pc := fun s => EvmInv s ∧ ¬ EvmDone s) (Ph := GPh R0 L0 F0)
                    h1 ?_ ?_ ?_ ?_ (fun r t h h' => ga_other p0 R0 L0 F0 r t h h')
                  · intro F t values body callee ret _ hP _ _
                    exact ⟨evmInv_entry callee hP.1.1, fun hd => hP.2.2.1
                      ((evmDone_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl).1 hd)⟩
                  · intro F t callee post v _ hP hq
                    obtain ⟨hi, hlt⟩ := hq.1 ⟨v, rfl⟩
                    refine ⟨fun _ => Or.inr ⟨evmInv_locals _ hi, ?_, hP.2.1⟩, fun h => absurd rfl h⟩
                    rw [(evm_congr (s := post) (t := { post with locals := t.locals }) rfl rfl).1]
                    rw [(evm_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl).1,
                      hP.1.2.1] at hlt
                    exact hlt
                  · intro F t callee post v _ hP hq
                    obtain ⟨hi, hlen, hR⟩ := hq.2 ⟨v, rfl⟩
                    obtain ⟨-, eR, eL, -⟩ := evm_congr (s := t) (t := callEntryStateHOLFinite t callee)
                      rfl rfl
                    obtain ⟨-, fR, fL, -⟩ := evm_congr (s := post)
                      (t := setVarHOLFinite (ofString "err") v { post with locals := t.locals }) rfl rfl
                    refine ⟨evmInv_setVar _ _ (evmInv_locals _ hi), ?_, ?_, ?_, hP.2.2.2⟩
                    · rw [fL, hlen, eL]; exact hP.1.2.2.2.1
                    · rw [fR]; exact hR.trans (le_of_eq (eR.trans hP.1.2.2.1))
                    · rw [locN_setVar_ne _ "done" (ofString "err") _ (by decide)]; exact hP.2.1
                  · refine Hoare.call0 (Pc := EvmInv) h2 ?_ ?_
                      (fun r t h h' => ga_other p0 R0 L0 F0 r t h h')
                    · intro F t values body callee ret _ hP _ _
                      exact evmInv_entry callee hP.1
                    · intro F u callee post v _ hP hq
                      obtain ⟨hi, hd, hlen, hR⟩ := hq v rfl
                      obtain ⟨-, eR, eL, -⟩ := evm_congr (s := u)
                        (t := callEntryStateHOLFinite u callee) rfl rfl
                      obtain ⟨fp, fR, fL, fF⟩ := evm_congr (s := post)
                        (t := { post with locals := u.locals }) rfl rfl
                      refine ⟨fun _ => Or.inr ⟨evmInv_locals _ hi, ?_, hP.2.2.2.1⟩,
                        fun h => absurd rfl h⟩
                      apply hfin _ (evmInv_locals _ hi)
                      · rw [fR]; exact hR.trans ((le_of_eq eR).trans hP.2.2.1)
                      · rw [fF, evmFp_done hd, hlen, eL, hP.2.1, hP.2.2.2.2]; omega
      · -- the done branch
        refine Hoare.ite ?_ ?_ (fun _ _ => gq_other p0 _ _ (by simp) (by simp))
        · refine Hoare.seq (R := GPdone p0 R0 L0 F0)
            (Hoare.skip fun t hP => ⟨fun _ => ?_, fun h => absurd rfl h⟩) ?_
          · rcases hP.1 with ⟨hp, hd, _⟩ | ⟨_, _, hz⟩
            · exact ⟨hp, hd⟩
            · exact absurd hz (condTrue_local_ne0 hP.2)
          refine Hoare.seq (R := GPepi R0 L0 F0) ?_ ?_
          · refine Hoare.call0 (Pc := fun s => EvmInv s ∧ EvmDone s) h3 ?_ ?_
              (fun r t h h' => ⟨fun hr => absurd hr h, fun _ => gq_other p0 r t h h'⟩)
            · intro F t values body callee ret _ hP _ _
              exact ⟨evmInv_entry callee hP.1.1,
                (evmDone_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl).2 hP.2⟩
            · intro F t callee post v _ hP hq
              obtain ⟨hi, hd, hlen, hR⟩ := hq v rfl
              obtain ⟨-, eR, eL, -⟩ := evm_congr (s := t) (t := callEntryStateHOLFinite t callee)
                rfl rfl
              obtain ⟨-, fR, fL, -⟩ := evm_congr (s := post) (t := { post with locals := t.locals })
                rfl rfl
              refine ⟨fun _ => ⟨evmInv_locals _ hi,
                (evmDone_congr (s := post) (t := { post with locals := t.locals }) rfl rfl).2 hd,
                ?_, ?_, ?_⟩, fun h => absurd rfl h⟩
              · rw [fL, hlen, eL]; exact hP.1.2.2.2.1
              · rw [fR]; exact hR.trans (le_of_eq (eR.trans hP.1.2.2.1))
              · rw [← hP.1.2.2.2.2, evmFp_done hP.2, hP.1.2.2.2.1]
          · refine Hoare.ite ?_ ?_ (fun _ _ => gq_other p0 _ _ (by simp) (by simp))
            · -- outermost frame: `ev`, `cur_cont` restored, `go := 0`
              refine Hoare.seq (R := fun _ => True)
                (Hoare.assign (fun _ _ _ _ => ⟨fun _ => trivial, fun h => absurd rfl h⟩)
                  (fun _ _ => ⟨fun h => absurd h (by simp), fun _ => gq_other p0 _ _ (by simp)
                    (by simp)⟩)) ?_
              refine Hoare.seq (R := fun _ => True)
                (Hoare.assign (fun _ _ _ _ => ⟨fun _ => trivial, fun h => absurd rfl h⟩)
                  (fun _ _ => ⟨fun h => absurd h (by simp), fun _ => gq_other p0 _ _ (by simp)
                    (by simp)⟩)) ?_
              refine Hoare.assign (fun t v _ hv => ?_) (fun _ _ => gq_other p0 _ _ (by simp) (by simp))
              cases evalAt_const t 0 v hv
              intro _
              right
              show locN (setVarHOLFinite (ofString "go") (.val (.word 0)) t) "go" = 0
              rw [locN_setVar_same]; rfl
            · -- pop the done child
              refine Hoare.dec (names := ["go"]) (P' := GPfin R0 L0 F0) (by decide) ?_ ?_
                (gq_postLocals p0) (fun _ _ => gq_other p0 _ _ (by simp) (by simp))
              · intro F t v hP hv
                cases evalAt_const t 0 v hv
                obtain ⟨⟨hi, hd, hlen, hR, hF⟩, hk⟩ := hP
                obtain ⟨-, fR, fL, -⟩ := evm_congr (s := t) (t := setVarHOLFinite _ _ t) rfl rfl
                refine ⟨⟨evmInv_setVar _ _ hi,
                  (evmDone_congr (s := t) (t := setVarHOLFinite _ _ t) rfl rfl).2 hd,
                  fL.trans hlen, (le_of_eq fR).trans hR, hF⟩, ?_⟩
                show memW t (globN t "cur_cont" + 16) ≠ 0
                have := condFalse_eq0 hk
                simpa using this
              · refine Hoare.callH
                  (Pc := fun s => EvmInv s ∧ EvmDone s ∧ memW s (globN s "cur_cont" + 16) ≠ 0)
                  (Ph := GPh4 R0 L0 F0) h4 ?_ ?_ ?_ ?_ (fun r t h h' => gq_other p0 r t h h')
                · intro F t values body callee ret _ hP _ _
                  exact ⟨evmInv_entry callee hP.1.1,
                    (evmDone_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl).2
                      hP.1.2.1, hP.2⟩
                · intro F t callee post v _ hP hq
                  obtain ⟨hi, hlen, hR⟩ := hq (Or.inl ⟨v, rfl⟩)
                  obtain ⟨-, eR, eL, -⟩ := evm_congr (s := t) (t := callEntryStateHOLFinite t callee)
                    rfl rfl
                  obtain ⟨-, fR, fL, fF⟩ := evm_congr (s := post)
                    (t := { post with locals := t.locals }) rfl rfl
                  intro _
                  left
                  refine ⟨evmInv_locals _ hi, hfin _ (evmInv_locals _ hi) ?_ ?_⟩
                  · rw [fR]; exact hR.trans ((le_of_eq eR).trans hP.1.2.2.2.1)
                  · rw [fF]
                    have h1 := evmFp_le post
                    have h2 := hP.1.2.2.2.2
                    rw [eL, hP.1.2.2.1] at hlen
                    omega
                · intro F t callee post v _ hP hq
                  obtain ⟨hi, hlen, hR⟩ := hq (Or.inr ⟨v, rfl⟩)
                  obtain ⟨-, eR, eL, -⟩ := evm_congr (s := t) (t := callEntryStateHOLFinite t callee)
                    rfl rfl
                  obtain ⟨-, fR, fL, -⟩ := evm_congr (s := post)
                    (t := setVarHOLFinite (ofString "err2") v { post with locals := t.locals }) rfl rfl
                  refine ⟨evmInv_setVar _ _ (evmInv_locals _ hi), ?_, ?_, hP.1.2.2.2.2⟩
                  · rw [fL, hlen, eL]; exact hP.1.2.2.1
                  · rw [fR]; exact hR.trans ((le_of_eq eR).trans hP.1.2.2.2.1)
                · refine Hoare.call0 (Pc := EvmInv) h2 ?_ ?_ (fun r t h h' => gq_other p0 r t h h')
                  · intro F t values body callee ret _ hP _ _
                    exact evmInv_entry callee hP.1
                  · intro F u callee post v _ hP hq
                    obtain ⟨hi, hd, hlen, hR⟩ := hq v rfl
                    obtain ⟨-, eR, eL, -⟩ := evm_congr (s := u)
                      (t := callEntryStateHOLFinite u callee) rfl rfl
                    obtain ⟨-, fR, fL, fF⟩ := evm_congr (s := post)
                      (t := { post with locals := u.locals }) rfl rfl
                    intro _
                    left
                    refine ⟨evmInv_locals _ hi, hfin _ (evmInv_locals _ hi) ?_ ?_⟩
                    · rw [fR]; exact hR.trans ((le_of_eq eR).trans hP.2.2.1)
                    · rw [fF, evmFp_done hd, hlen, eL]
                      have := hP.2.1
                      have := hP.2.2.2
                      omega
        · refine Hoare.skip (fun t hP => fun _ => ?_)
          rcases hP.1 with ⟨_, _, hn⟩ | ⟨hi, hp, _⟩
          · exact absurd (condFalse_local_ne0 hP.2) hn
          · exact Or.inl ⟨hi, hp⟩
  have hnt : (evaluateHOLFiniteState (decClockHOLFinite s) b).1 ≠ some .timeOut := by
    rcases hflow with h | h <;> rw [h] <;> simp
  have hpre : GPre p0 R0 L0 F0 (decClockHOLFinite s) := by
    obtain ⟨e1, e2, e3, e4⟩ := evm_congr (s := s) (t := decClockHOLFinite s) rfl rfl
    exact ⟨localsFree_evmInv s s.locals (s.clock - 1) hinv, e1, e2, e3, e4⟩
  exact key.run (decClockHOLFinite s) hcode hpre hnt hflow

/-- One continuing iteration of the `run_frames` loop strictly lowers `evmPot` and keeps
`EvmInv`, or ends the loop (`go := 0` after the outermost frame). Proved from the four contract
leaves and the (proved) glue. -/
theorem run_frames_step : ∀ c b, runFramesLoop = some (c, b) →
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → EvmInv s →
      LoopActive c s →
      ((evaluateHOLFiniteState (decClockHOLFinite s) b).1 = none ∨
        (evaluateHOLFiniteState (decClockHOLFinite s) b).1 = some .continue) →
      (EvmInv (evaluateHOLFiniteState (decClockHOLFinite s) b).2 ∧
        evmPot (evaluateHOLFiniteState (decClockHOLFinite s) b).2 < evmPot s) ∨
      locN (evaluateHOLFiniteState (decClockHOLFinite s) b).2 "go" = 0 :=
  run_frames_step_of_specs op_dispatch_spec frame_exception_spec frame_epilogue_spec
    finish_child_spec

/-! ### Concrete compositions (revision 4: shrinking the primitive list) -/

theorem TerminatingProgBoundedOn.mono_bound {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {prog : ProgHOL 64} {a b : Nat} (h : TerminatingProgBoundedOn P prog a) (hle : a ≤ b) :
    TerminatingProgBoundedOn P prog b :=
  fun s hc hP => (h s hc hP).weaken hle

/-- A program that never changes the clock costs nothing. -/
theorem TerminatingProgBoundedOn.of_clock {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {prog : ProgHOL 64}
    (h : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), (evaluateHOLFiniteState s prog).2.clock = s.clock) :
    TerminatingProgBoundedOn P prog 0 :=
  fun s _ _ _ => ⟨by have := h s; omega, by have := h s; omega⟩

theorem clock_return {F : Type} (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) :
    (evaluateHOLFiniteState s (.return e)).2.clock = s.clock := by
  rw [evaluateHOLFiniteState_return]
  repeat' split
  all_goals (try dsimp only)
  all_goals (try split)
  all_goals (try rfl)

theorem clock_raise {F : Type} (s : PanSemStateFiniteExact 64 F) (n : MlS) (e : ExpHOL 64) :
    (evaluateHOLFiniteState s (.raise n e)).2.clock = s.clock := by
  rw [evaluateHOLFiniteState_raise]
  repeat' split
  all_goals (try dsimp only)
  all_goals (try split)
  all_goals (try rfl)

theorem clock_shMemStore {F : Type} (s : PanSemStateFiniteExact 64 F) (op : OpSize) (a v : ExpHOL 64) :
    (evaluateHOLFiniteState s (.shMemStore op a v)).2.clock = s.clock := by
  rw [evaluateHOLFiniteState_shMemStore]
  show (shMemStoreClauseHOLFiniteExact s op a v).2.clock = s.clock
  simp only [shMemStoreClauseHOLFiniteExact, shMemStoreClauseHOLExact, shMemStoreHOLExact]
  repeat' split
  all_goals rfl

/-- A guard that ignores locals and clock holds at every callee entry. -/
theorem callEntryOn_of_localsFree {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (h : LocalsFree P) (fname : MlS) (arguments : List (ExpHOL 64)) :
    CallEntryOn P P fname arguments :=
  fun state _ _ _ _ _ hP _ _ => h state _ _ hP

/-- `seq` whose second part needs only `GuestInv` (which every evaluation keeps). -/
theorem TerminatingProgBoundedOn.seq_guestInv_after
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {first second : ProgHOL 64} {a b : Nat}
    (h1 : TerminatingProgBoundedOn P first a)
    (hPG : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → GuestInv s)
    (h2 : TerminatingProgBoundedOn GuestInv second b) :
    TerminatingProgBoundedOn P (.seq first second) (a + b) := by
  intro F state hcode hP
  have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata state first
  have hmid := guestInv_evaluate state first (hPG state hP)
  unfold TerminatingRunBounded
  dsimp only
  intro hnt
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rcases hr1 : evaluateHOLFiniteState state first with ⟨r1, mid⟩
  simp only [hr1] at hmeta hnt hmid ⊢
  cases r1 with
  | none =>
    dsimp only at hnt ⊢
    have hnt1 : (evaluateHOLFiniteState state first).1 ≠ some .timeOut := by simp [hr1]
    obtain ⟨s1, k1⟩ := h1 state hcode hP hnt1
    rw [hr1] at s1 k1
    dsimp only at s1 k1
    obtain ⟨s2, k2⟩ := h2 mid (hmeta.1.trans hcode) hmid hnt
    exact ⟨by omega, by omega⟩
  | some r =>
    dsimp only at hnt ⊢
    have hnt1 : (evaluateHOLFiniteState state first).1 ≠ some .timeOut := by simpa [hr1] using hnt
    obtain ⟨s1, k1⟩ := h1 state hcode hP hnt1
    rw [hr1] at s1 k1
    dsimp only at s1 k1
    exact ⟨by omega, k1⟩

theorem seq_clock {first second : ProgHOL 64}
    (h1 : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), (evaluateHOLFiniteState s first).2.clock = s.clock)
    (h2 : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), (evaluateHOLFiniteState s second).2.clock = s.clock) :
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), (evaluateHOLFiniteState s (.seq first second)).2.clock = s.clock := by
  intro F s
  rw [evaluateHOLFiniteState_seq_line780]
  rcases hr : evaluateHOLFiniteState s first with ⟨r, mid⟩
  have := h1 s
  rw [hr] at this
  cases r with
  | none => dsimp only; rw [h2 mid]; exact this
  | some _ => exact this

theorem clock_assign {F : Type} (s : PanSemStateFiniteExact 64 F) (k : VarKind) (n : MlS)
    (e : ExpHOL 64) : (evaluateHOLFiniteState s (.assign k n e)).2.clock = s.clock := by
  rw [evaluateHOLFiniteState_assign]
  repeat' split
  all_goals (try dsimp only)
  all_goals (try split)
  all_goals (try rfl)
  all_goals (cases k <;> rfl)

/-- A guard implied by the caller's guard holds at every callee entry, if it ignores locals. -/
theorem callEntryOn_of_imp {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hQ : LocalsFree Q) (himp : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → Q s)
    (fname : MlS) (arguments : List (ExpHOL 64)) : CallEntryOn P Q fname arguments :=
  fun state _ _ _ _ _ hP _ _ => hQ state _ _ (himp state hP)

/-- The continuation of any `decCall` is a `GuestInv` state. -/
theorem decCallResumeOn_guestInv {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hPG : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → GuestInv s)
    (name fname : MlS) (arguments : List (ExpHOL 64)) :
    DecCallResumeOn P GuestInv name fname arguments := by
  intro F state values body callee ret value post _ hP _ _ hrun
  have hpost := guestInv_evaluate (callEntryStateHOLFinite state callee) body
    (guestInv_callEntry state callee (hPG state hP))
  rw [hrun] at hpost
  exact guestInv_setVar name value _ (guestInv_with_locals_clock post state.locals post.clock hpost)

/-- A read-only callee resumes its caller in the caller's guard (the declared name is not read by
the guard). -/
theorem ReadOnlyFn.resumeOn {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {names : List String} (hP : LocalsOnly names P)
    (hPG : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → GuestInv s)
    {fname : MlS} (h : ReadOnlyFn fname) (name : MlS) (hname : ∀ n ∈ names, ofString n ≠ name)
    (arguments : List (ExpHOL 64)) : DecCallResumeOn P P name fname arguments := by
  obtain ⟨params, body', ret', hlook, hb⟩ := h
  intro F state values body callee ret value post hcode hPs _ hl hrun
  have hsame := lookupCodeHOLFinite_installed_body state.code.lookup fname params body' body
    ret' ret values callee (by rw [hcode]; exact hlook) hl
  subst hsame
  have hro := hb (callEntryStateHOLFinite state callee) hcode
    (guestInv_callEntry state callee (hPG state hPs)) (by rw [hrun]; simp) (by rw [hrun]; exact Or.inl ⟨value, rfl⟩)
  rw [hrun] at hro
  dsimp only at hro
  have heq : ({ post with locals := state.locals } : PanSemStateFiniteExact 64 F) =
      { state with locals := state.locals, clock := post.clock } := by
    rw [hro]; rfl
  rw [heq]
  exact hP.setVar hname value _ (hP state state.locals post.clock (fun _ _ => rfl) hPs)
