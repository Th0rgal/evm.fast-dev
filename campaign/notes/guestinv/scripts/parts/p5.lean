
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
allocator pointers changes (round-3 Gemini item 5: the globals frame was missing). Revision 8
(round-5 Gemini item 2): the new table has the requested key length (`htab_new` stores `key_len` at
`t+0`), which the callers need for the role key lengths of `RolesOK`. -/
def HtabNewExit : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
    PanSemStateFiniteExact 64 F → Prop :=
  fun s r post => ∀ v, r = some (.returned v) → ∃ w : BitVec 64, v = .val (.word w) ∧
    ArenaReady post ∧ HtabWF post w.toNat ∧ hdr post w.toNat 3 = 0 ∧
    hdr post w.toNat 0 = locN s "key_len" ∧
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

/-- Entry of the two MPT update functions `_mpt_insert_node`/`_mpt_delete_node(_body)(node, key,
klen, level, …)`: separated arenas and a typed trie below the `node` parameter. Revision 6
(round-4 Astra item 5): `level ≤ klen` and the unread key `(key + level, klen − level)` is a
nibble array next to the trie (`KeyIn`: nibbles, allocated heap, disjoint from every node record).
Both loops read `loadByte(key + level)` as a branch index and store through `node + 32 + 8·idx`
(insert) or push it into a scratch frame that later stores `fnode + 32 + 8·idx` (delete). A key
byte `18` indexed `n + 176`, past the 176-byte branch. `level` grows by `1` at a branch (only when
`level ≠ klen`) and by an extension's path length when `common_prefix_length` matched all of it
(`≤ klen − level`), so `level ≤ klen` and the key's suffix are loop invariants; the writes go to
node records, fresh heap and the free scratch gap, which `KeyIn` keeps away from the key. -/
def MptReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ locN s "level" ≤ locN s "klen" ∧ ∃ Nd, NodeHeap s Nd ∧
    RootIn Nd (locN s "node") ∧
    KeyIn s Nd (locN s "key" + locN s "level") (locN s "klen" - locN s "level")

/-- The trie object `m` (16 bytes, `mpt_new` 10446: `+0` root node) and its node set, placed
relative to the typed world `S` (revision 5, round-4 Fable item 3): `m` is allocated, and `m` and
every node of `Nd` are disjoint from every table footprint of `S` and every fixed object, as
`TriesTyped` requires of the world tries. `mpt_set` stores `m+0` (10886) and rewrites node records;
`mpt_root` stores hash pointers into the node caches (`+8/+16`). A node at `nodes + 8` of a table
in `S` made `mpt_root` overwrite that table's root. Revision 6: the node paths too
(`nodeExtents`, round-4 Astra item 5), and `m` avoids the persistent tries (`AvoidsTries`, item
2: `mpt_set`'s store `m+0` must not hit a world node). -/
def MptObjInWith {F : Type} (s : PanSemStateFiniteExact 64 F) (S Nm : List Nat) (m : Nat) : Prop :=
  Allocated s (m, 16) ∧ WordsOK s (m, 16) ∧
  (∀ t ∈ S, ∀ i ∈ htabFootprint s t, Disj (m, 16) i) ∧
  (∀ j ∈ fixedObjects s, Disj (m, 16) j) ∧
  NodeHeap s Nm ∧ RootIn Nm (memW s m) ∧
    ∀ o ∈ nodeExtents s Nm, Disj o (m, 16) ∧
      (∀ t ∈ S, ∀ i ∈ htabFootprint s t, Disj o i) ∧
      ∀ j ∈ fixedObjects s, Disj o j

/-- Revision 7: `MptObjIn` with the trie object's node set `Nm` and address `m` exposed
(`MptObjInWith`), so that the relational contracts `MptObjStep` and `mpt_from_witness`'s return
typing can name them. Logically the revision-6 definition. -/
def MptObjIn {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat) : Prop :=
  ∃ Nm, MptObjInWith s S Nm (locN s "m")

/-- A typed world `S` with a typed trie object `m` in it (`MptObjIn`, the same `S`), and regions
`R s` disjoint from every table footprint of `S` and every fixed object (`mpt_root`'s output
buffer, as in `WorldAvoids`). Revision 6 (round-4 Astra item 2): the object `m` and the regions
avoid the persistent tries (`AvoidsTries`, same `S`). Revision 8 (round-5 Fable non-blocking): one
typing `(Nm, Nd)` has the object's node extents disjoint from the persistent tries' too, as
`RetMptObj` and `MptObjStep` state. -/
def MptObjAvoids (R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ ∃ S, WorldTyped s S ∧ MptObjIn s S ∧ (∀ i ∈ R s,
    (∀ t ∈ S, ∀ j ∈ htabFootprint s t, Disj i j) ∧ ∀ j ∈ fixedObjects s, Disj i j) ∧
    AvoidsTries s S ((locN s "m", 16) :: R s) ∧
    ∃ Nm Nd, MptObjInWith s S Nm (locN s "m") ∧ TriesTypedWith s S Nd ∧
      ∀ o ∈ (locN s "m", 16) :: R s ++ nodeExtents s Nm, ∀ j ∈ nodeExtents s Nd, Disj o j

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

/-- `_mpt_insert_node` under `MptReady`. `MptExit` constrains normal returns only. On a cycle of
empty extension segments (`sl = 0`, `node := node+48`, e.g. two extensions pointing at each other;
`NodeHeap` does not exclude it) the loop never returns: it reaches `WhileTimesOut` within the
`2^130` iteration bound of its `GUARD` measure (DESIGN.md §3), so the bound leaf still holds and
this spec is vacuous on such runs (round-4 Gemini non-blocking). -/
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

/-- `rollback_child_access(child)`: the child's two access tables are typed. Revision 6 (found
while auditing the `gbody_*` hypotheses, round-4 Astra item 8): the body truncates `child+168`,
then RELOADS `child+176` and `child+272` and truncates that table, so its composition needs the
child record outside both footprints, allocated words, and the two tables equal or with disjoint
footprints (`htab_truncate_spec` frames only the first table's footprint). `finish_child` calls it
after `ev := parent`, from facts it read off `EvmInv` while `child` was the current frame (record
and tables of a chain frame: `FrameWF`, frame objects disjoint from table footprints, tables of `S`
pairwise disjoint). -/
def RollbackReadyAt {F : Type} (s : PanSemStateFiniteExact 64 F) (c : Nat) : Prop :=
  ArenaReady s ∧ Allocated s (c, 280) ∧ WordsOK s (c, 280) ∧
    (∀ k ∈ [168, 176],
      HtabWF s (memW s (c + k)) ∧
      ∀ i ∈ htabFootprint s (memW s (c + k)), Allocated s i ∧ Disj (c, 280) i) ∧
    (memW s (c + 168) = memW s (c + 176) ∨
      ∀ i ∈ htabFootprint s (memW s (c + 168)), ∀ j ∈ htabFootprint s (memW s (c + 176)), Disj i j)

def RollbackReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => RollbackReadyAt s (locN s "child")

/-- Revision 7 (round-4 Gemini item 1(b)): the current frame of an `EvmInv` state is
`RollbackReadyAt` (PROVED). `finish_child` reads `child := ev` and calls `rollback_child_access(child)`
after `create_finish`/`state_restore`/`refill_frame_state_gas`/`frame_halt` (`EvmStep`: `ev` kept,
`EvmInv` again) and after `ev := parent` (memory unchanged), so its walk obtains the callee's guard
from this lemma at the last `EvmInv` state with `ev = child`. -/
theorem rollbackReadyAt_of_evmInv {F : Type} (s : PanSemStateFiniteExact 64 F) (h : EvmInv s) :
    RollbackReadyAt s (globN s "ev") := by
  obtain ⟨hA, S, hW, hrest⟩ := h
  obtain ⟨hT, -, -, -⟩ := hW
  obtain ⟨-, hTt, hTp, -⟩ := hT
  dsimp only at hrest
  obtain ⟨-, -, -, hWF, -, -, -, hdis, -⟩ := hrest
  have hmem : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
    simp [evmChain, evmChainFrom]
  have hF := hWF _ hmem
  dsimp only [FrameWF] at hF
  obtain ⟨hblk, -, -, -, -, -, -, -, h168, h176, -⟩ := hF
  have hrec := hblk (globN s "ev", 280) (by simp)
  have hd := hdis _ hmem (globN s "ev", 280) (by simp [frameObjects])
  refine ⟨hA, Or.inr hrec.1, hrec.2, ?_, ?_⟩
  · intro k hk
    have hS : memW s (globN s "ev" + k) ∈ S := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl
      · exact h168
      · exact h176
    exact ⟨(hTt _ hS).1, fun i hi => ⟨((hTt _ hS).2 i hi).1, hd.1 _ hS i hi⟩⟩
  · by_cases heq : memW s (globN s "ev" + 168) = memW s (globN s "ev" + 176)
    · exact Or.inl heq
    · exact Or.inr (hTp _ h168 _ h176 heq)

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

theorem localsOnly_mptReady : LocalsOnly ["node", "key", "klen", "level"] MptReady := by
  intro F s locals k hl hP
  have ht := locN_congr s locals k "node" (hl "node" (by simp))
  have hk := locN_congr s locals k "key" (hl "key" (by simp))
  have hn := locN_congr s locals k "klen" (hl "klen" (by simp))
  have hv := locN_congr s locals k "level" (hl "level" (by simp))
  simp only [MptReady, arenaReady_with_locals] at hP ⊢
  rw [ht, hk, hn, hv]
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
  simp only [RollbackReady, RollbackReadyAt, htabWF_with_locals, arenaReady_with_locals] at hP ⊢
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
only inside `R s` and the memory free at entry, and only the globals in `gw` change. Revision 8
(round-5 Astra item 7): the scratch arena only grows too (`scratch_ptr` never rises: every writer
in this tier releases scratch only to marks it took itself), so a caller's scratch records stay
allocated and a loop pushing scratch records has a strictly decreasing `scratch_ptr`. -/
def WritesWithin (R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl) (gw : List String)
    (fname : MlS) : Prop :=
  FunSpec ArenaReady (fun s r post => Resumes r →
    ArenaReady post ∧ globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
    globN post "scratch_ptr" ≤ globN s "scratch_ptr" ∧
    FrameOutside s post
      (R s ++ [(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")])
      (globN s "heap_ptr", heapLimit - globN s "heap_ptr") ∧
    ∀ name, name ∉ gw → s.globals.lookup (ofString name) = post.globals.lookup (ofString name))
    fname

/-- `WorldOK`, and the regions `R s` are disjoint from every typed table and fixed object and
(revision 6, round-4 Astra item 2) from the persistent tries (`AvoidsTries`, same `S`): the output
buffers of `compute_state_root`/`build_mpt_indexed` must not overwrite a trie node or path. -/
def WorldAvoids (R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ ∃ S, WorldTyped s S ∧ (∀ i ∈ R s,
    (∀ t ∈ S, ∀ j ∈ htabFootprint s t, Disj i j) ∧ ∀ j ∈ fixedObjects s, Disj i j) ∧
    AvoidsTries s S (R s)

/-- `process_transaction(tx, index)` writes the receipt slots `bo+24`/`bo+32` at `16·index`
(33368-33374): the index is below the block's transaction count `bo+80` (`execute_block`'s loop).
Revision 8 (round-5 Fable item 2): `bo` and the two arrays are non-null. `blockOutObjects` reads a
null array as an empty object, so with `bo+24 = 0` the stores went to `16·index`, which a suitable
index puts on a typed table's header. `execute_block` stores the two `alloc` results (nonzero heap
blocks) before its loop, and every callee in between keeps `bo` and the words `bo+24`, `bo+32`
(`GlobalsKept`, `RecordsKept`). -/
def TxReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => WorldOK s ∧ globN s "bo" ≠ 0 ∧ memW s (globN s "bo" + 24) ≠ 0 ∧
    memW s (globN s "bo" + 32) ≠ 0 ∧ locN s "index" < memW s (globN s "bo" + 80)

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
`validate_transaction`, `30000000` for system calls) bounds the initial `R` of `EvmInv`.
Revision 6 (round-4 Astra item 2): the record also avoids the persistent tries (`AvoidsTries`);
every caller passes a fresh `msg_new` block. Revision 7: the record is in the HEAP (`msg_new` uses
`alloc`), so it stays allocated across every world step (the heap only grows; `scratch_ptr` is in
most callees' write set). Revision 8 (round-5 Gemini item 1): the two tables have the frame roles
`frame.addr`/`frame.key` (`RolesOK`), so they are distinct from each other and from every world
slot (`frame_new` makes them the outermost frame's `e+168`/`e+176`). -/
def MsgReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ ∃ S, WorldTyped s S ∧
    memW s (locN s "msg" + 152) ∈ S ∧ memW s (locN s "msg" + 160) ∈ S ∧
    Inside (locN s "msg", 176) sourceBase (globN s "heap_ptr") ∧ WordsOK s (locN s "msg", 176) ∧
    (∀ t ∈ S, ∀ i ∈ htabFootprint s t, Disj (locN s "msg", 176) i) ∧
    (∀ j ∈ fixedObjects s, Disj (locN s "msg", 176) j) ∧
    AvoidsTries s S [(locN s "msg", 176)] ∧
    memW s (locN s "msg" + 40) < 2 ^ 63 ∧
    RolesOK s S (worldRoleSlots s ++
      [(memW s (locN s "msg" + 152), "frame.addr"), (memW s (locN s "msg" + 160), "frame.key")])
      (journalRoleSlots s)

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
    AvoidsTries s S (ch.map (frameObjects s)).flatten ∧
    MarksOK s S ch ∧
    RolesOK s S (worldRoleSlots s ++ frameRoleSlots s ch) (journalRoleSlots s) ∧
    (ch.map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum + 1 < 2 ^ 64

theorem evmInv_iff_at {F : Type} (s : PanSemStateFiniteExact 64 F) :
    EvmInv s ↔ ArenaReady s ∧ ∃ S, EvmInvAt s S := Iff.rfl

/-- The 176-byte message record at `m` is owned (as in `MsgReady`): allocated words, disjoint
from every table footprint of `S`, every fixed object, every frame block of the chain and
(revision 6, round-4 Astra item 2) the persistent tries. -/
def MsgOwned {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat) (m : Nat) : Prop :=
  Allocated s (m, 176) ∧ WordsOK s (m, 176) ∧
  (∀ t ∈ S, ∀ i ∈ htabFootprint s t, Disj (m, 176) i) ∧
  (∀ j ∈ fixedObjects s, Disj (m, 176) j) ∧
  (∀ ec ∈ evmChain s, ∀ o ∈ frameObjects s ec, Disj (m, 176) o) ∧
  AvoidsTries s S [(m, 176)]

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

/-- The node parameter `x` is a node of `Nd` of kind `k` (revision 6, round-4 Astra item 6). -/
def NodeKind {F : Type} (s : PanSemStateFiniteExact 64 F) (Nd : List Nat) (x : String) (k : Nat) :
    Prop :=
  locN s x ∈ Nd ∧ memW s (locN s x) = k

/-- MPT-tier callee entry (round-3 item 5, DESIGN.md Q9): separated arenas, the listed node
parameters are rooted in a typed node heap `Nd`, and the function's own requirement `req s Nd`
(revision 6, round-4 Astra items 5 and 6): the node kinds it reads and writes (`NodeKind`), and
the nibble arrays it indexes or copies into a node path (`KeyIn`). -/
def NodeArgs (names : List String)
    (req : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Nat → Prop) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ ∃ Nd, NodeHeap s Nd ∧ (∀ n ∈ names, RootIn Nd (locN s n)) ∧ req s Nd

/-- MPT-tier callee exit, `MptExit`-shaped: every typed node set satisfying the entry extends to a
typed node set of the post-state; memory changes only inside those node records, the free scratch
gap and the heap free at entry; the returned word is a typed node or `0` (what `_mpt_insert_node` /
`_mpt_delete_node_body` need to re-establish `MptReady` at their loop heads). The node functions
write no global buffer (checked on their closures). Revision 6: the old nodes keep their kinds and
every new node of `Nd'` is a fresh heap record (all seven functions write node fields `+8` and
beyond, and build nodes only with `alloc`). The callers' loop invariants need both: a saved
extension stays an extension until `_delete_ext_finish`, and a key or saved path stays disjoint
from the grown node set. -/
def NodeFnExit (names : List String)
    (req : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Nat → Prop) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F →
    Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop :=
  fun s r post => Resumes r → ArenaReady post ∧ globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
    ∀ Nd, NodeHeap s Nd → (∀ n ∈ names, RootIn Nd (locN s n)) → req s Nd →
      ∃ Nd', NodeHeap post Nd' ∧ (∀ n ∈ Nd, n ∈ Nd') ∧
        (∀ n ∈ Nd, memW post n = memW s n) ∧
        (∀ n ∈ Nd', n ∈ Nd ∨ Inside (nodeIvl post n) (globN s "heap_ptr") (globN post "heap_ptr")) ∧
        FrameOutside s post
          ((Nd.map fun n => nodeIvl s n) ++
            [(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")])
          (globN s "heap_ptr", heapLimit - globN s "heap_ptr") ∧
        (∀ name, name ∉ ["heap_ptr", "scratch_ptr"] →
          s.globals.lookup (ofString name) = post.globals.lookup (ofString name)) ∧
        ∀ v, r = some (.returned v) → ∃ w : BitVec 64, v = .val (.word w) ∧ RootIn Nd' w.toNat

/-- `NodeFn names req g`: from a typed node heap rooting `names` and meeting `g`'s requirement
`req` (node kinds, key arrays; DESIGN.md §6 "NodeFn requirements"), `g` ends in a typed node heap. -/
def NodeFn (names : List String)
    (req : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Nat → Prop) (fname : MlS) : Prop :=
  FunSpec (NodeArgs names req) (NodeFnExit names req) fname

/-- Value contract (revision 6): a normal return is a word at most `B` of the entry state.
`common_prefix_length(a, al, b, bl)` returns `i < min(al, bl)` or `min(al, bl)` (AST 10512); the
MPT loops need `pl ≤ sl` and `pl ≤ klen − level` to keep `level ≤ klen` and to meet
`_split_extension`'s requirement `pl < sl`. -/
def RetLe (B : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat) (fname : MlS) : Prop :=
  FunSpec GuestInv (fun s r _ => ∀ v, r = some (.returned v) →
    ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat ≤ B s) fname

/-- Value contract (revision 6): a normal return is a pair `(p, l)` of a nibble array allocated
fresh on the heap during the call. `mpt_nibble_key` (AST 10470) returns `alloc(64)` filled by
`key_to_nibbles` from the 32-byte hash, or `alloc(2·klen)` filled from the key: the key
`_mpt_insert_node`/`_mpt_delete_node` receive from `mpt_set` (`MptReady`'s `KeyIn`). -/
def RetNibbles (fname : MlS) : Prop :=
  FunSpec ArenaReady (fun s r post => ∀ v, r = some (.returned v) →
    ∃ p l : BitVec 64, v = .rStruct [.val (.word p), .val (.word l)] ∧
      NibblesOK post p.toNat l.toNat ∧
      Inside (p.toNat, l.toNat) (globN s "heap_ptr") (globN post "heap_ptr")) fname

/-- `requests_append` entry: the next request slot exists. -/
def ReqRoom : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => WorldOK s ∧ memW s (globN s "bo" + 64) < 8

/-! ### Relational callee contracts (revision 7, round-4 Gemini item 1)

Revision 6 stated the callee contracts of the world tier as `KeepsOn WorldOK WorldOK`: from a
`WorldOK` entry the callee ends in SOME `WorldOK` state. A caller holding local facts across such a
call (its fresh message record, its fresh tables, `bo+64`, `bo+80`, `index < ntx`, a fresh output
buffer) lost them all, so several `gbody_*` were not provable from their own hypotheses. Every
callee contract at a world-tier call site is now RELATIONAL, `WorldStep R gw keep Q s r post`:
* the arenas stay separated and the heap only grows;
* every global outside the callee's write set `gw` (computed by `coverage.py` over the callee's
  closure) is unchanged;
* the words `keep` of the four typed records `ws`, `bs`, `ts`, `bo` that the callee's closure never
  stores to (computed by `coverage.py`) are unchanged;
* for EVERY typing `(S, Nd)` of the entry state whose typed memory the callee's own output regions
  `R s` avoid, the exit state is typed by some `S' ⊇ S` (so a caller's own tables in `S` stay
  typed tables), every world-owned interval of the exit lies inside a world-owned interval of the
  entry or in the heap allocated during the call (`OwnedGrows`: a caller's object disjoint from the
  world at entry stays disjoint from it), and memory outside the entry's world-owned intervals, the
  regions `R s`, the free scratch gap and the free heap is unchanged (a caller's object outside the
  world keeps its contents);
* a callee-specific extra `Q` (return typing, `bo+64` increment), stated for the same `S'`.

`EvmStep` is the EVM-tier analogue (`ev`, `cur_cont` and the chain `evmChain` kept), `MptObjStep`
carries a trie object `m` and its node set. -/

/-- `WorldTyped` with the persistent tries' node set `Nd` exposed. -/
def WorldTypedWith {F : Type} (s : PanSemStateFiniteExact 64 F) (S Nd : List Nat) : Prop :=
  TablesTyped s S ∧ JournalTyped s S ∧ FixedTyped s ∧ TriesTypedWith s S Nd

theorem worldTyped_iff_with {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat) :
    WorldTyped s S ↔ ∃ Nd, WorldTypedWith s S Nd := by
  simp only [WorldTyped, TriesTyped, WorldTypedWith]
  constructor
  · rintro ⟨h1, h2, h3, Nd, h4⟩
    exact ⟨Nd, h1, h2, h3, h4⟩
  · rintro ⟨Nd, h1, h2, h3, h4⟩
    exact ⟨h1, h2, h3, Nd, h4⟩

/-- The global records whose CONTENTS `WorldTyped` reads (table slots, trie root, block output). -/
def typedRecords : List (String × Nat) := [("ws", 40), ("bs", 80), ("ts", 72), ("bo", 88)]

/-- The memory `WorldTypedWith s S Nd` reads: table footprints, the four typed records, the
journal array, the block-output objects, the BAL objects and the trie nodes with their paths. The
other global buffers (`keccak_pad`, `bal_key_buf`, `evm_key_buf`, …) are owned but their contents
are untyped, so an output region may lie inside one of them. -/
def worldTypedIvls {F : Type} (s : PanSemStateFiniteExact 64 F) (S Nd : List Nat) : List Ivl :=
  S.flatMap (htabFootprint s) ++
    typedRecords.map (fun r => (globN s r.1, if globN s r.1 = 0 then 0 else r.2)) ++
    [(globN s "journal", 32 * globN s "journal_cap")] ++ blockOutObjects s ++ balObjects s ++
    nodeExtents s Nd

/-- Everything the world owns under the typing `(S, Nd)`. -/
def worldOwned {F : Type} (s : PanSemStateFiniteExact 64 F) (S Nd : List Nat) : List Ivl :=
  S.flatMap (htabFootprint s) ++ fixedObjects s ++ nodeExtents s Nd

def IvlsDisj (os js : List Ivl) : Prop := ∀ o ∈ os, ∀ j ∈ js, Disj o j

/-- Free scratch at `s` (between the frame-memory and scratch pointers). -/
def freeGap {F : Type} (s : PanSemStateFiniteExact 64 F) : Ivl :=
  (globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")

/-- Free heap at `s`. -/
def heapFree {F : Type} (s : PanSemStateFiniteExact 64 F) : Ivl :=
  (globN s "heap_ptr", heapLimit - globN s "heap_ptr")

/-- Only the globals in `gw` change. -/
def GlobalsKept (gw : List String) {F : Type} (s post : PanSemStateFiniteExact 64 F) : Prop :=
  ∀ name, name ∉ gw → s.globals.lookup (ofString name) = post.globals.lookup (ofString name)

/-- The listed words of the typed records are unchanged unless an output region hits them. -/
def RecordsKept (R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl)
    (keep : List (String × List Nat)) {F : Type} (s post : PanSemStateFiniteExact 64 F) : Prop :=
  ∀ r ∈ keep, globN s r.1 ≠ 0 → ∀ k ∈ r.2, (∀ i ∈ R s, ¬ CellHits (globN s r.1 + k) i) →
    memW post (globN s r.1 + k) = memW s (globN s r.1 + k)

/-- Every interval of `new` (an exit's owned intervals) is empty, inside an interval of `old` (the
entry's), or in the heap allocated between `s` and `post`. -/
def OwnedGrows {F : Type} (s post : PanSemStateFiniteExact 64 F) (old new : List Ivl) : Prop :=
  ∀ o ∈ new, o = (0, 0) ∨ (∃ j ∈ old, Inside o j.1 (j.1 + j.2)) ∨
    Inside o (globN s "heap_ptr") (globN post "heap_ptr")

/-- No callee-specific extra. -/
def NoExtra : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
    PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop :=
  fun _ _ _ _ _ => True

/-- The relational world step (see the section header). -/
def WorldStep (R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl) (gw : List String)
    (keep : List (String × List Nat))
    (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop :=
  fun s r post =>
    ArenaReady post ∧ globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
    GlobalsKept gw s post ∧ RecordsKept R keep s post ∧
    ∀ S Nd, WorldTypedWith s S Nd → IvlsDisj (R s) (worldTypedIvls s S Nd) →
      ∃ S' Nd', (∀ t ∈ S, t ∈ S') ∧ WorldTypedWith post S' Nd' ∧
        OwnedGrows s post (worldOwned s S Nd) (worldOwned post S' Nd') ∧
        FrameOutside s post (worldOwned s S Nd ++ R s ++ [freeGap s]) (heapFree s) ∧
        Q s r post S' Nd'

/-- From a `P` entry, every resuming outcome is a `WorldStep`. -/
def WorldKeeps (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl) (gw : List String)
    (keep : List (String × List Nat))
    (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop) (fname : MlS) : Prop :=
  FunSpec P (fun s r post => Resumes r → WorldStep R gw keep Q s r post) fname

/-- Revision 8 (round-5 Fable item 1): `WorldStep` quantified only over the entry typings whose
table set contains the tables `T s` the caller's guard owns. `MsgReady` makes the message's access
tables `msg+152`, `msg+160` typed in SOME `S`; `process_message_call` writes them (`frame_new`
copies them into the outermost frame, `warm_address`/`warm_storage_key` `htab_set` into them), so
for a typing `S₀` without them (still a typing) the write lay outside `worldOwned s S₀ Nd` and
`FrameOutside` failed. -/
def WorldStepIn (T : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Nat)
    (R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl) (gw : List String)
    (keep : List (String × List Nat))
    (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop :=
  fun s r post =>
    ArenaReady post ∧ globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
    GlobalsKept gw s post ∧ RecordsKept R keep s post ∧
    ∀ S Nd, WorldTypedWith s S Nd → (∀ t ∈ T s, t ∈ S) → IvlsDisj (R s) (worldTypedIvls s S Nd) →
      ∃ S' Nd', (∀ t ∈ S, t ∈ S') ∧ WorldTypedWith post S' Nd' ∧
        OwnedGrows s post (worldOwned s S Nd) (worldOwned post S' Nd') ∧
        FrameOutside s post (worldOwned s S Nd ++ R s ++ [freeGap s]) (heapFree s) ∧
        Q s r post S' Nd'

/-- From a `P` entry, every resuming outcome is a `WorldStepIn T`. -/
def WorldKeepsIn (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (T : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Nat)
    (R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl) (gw : List String)
    (keep : List (String × List Nat))
    (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop) (fname : MlS) : Prop :=
  FunSpec P (fun s r post => Resumes r → WorldStepIn T R gw keep Q s r post) fname

/-- A step over the typings containing `T s` ends in `WorldOK` (proved). -/
theorem WorldStepIn.worldOK {T : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Nat}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {F : Type} {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (h : WorldStepIn T R gw keep Q s r post)
    (hs : ∃ S Nd, WorldTypedWith s S Nd ∧ (∀ t ∈ T s, t ∈ S) ∧ IvlsDisj (R s) (worldTypedIvls s S Nd)) :
    WorldOK post := by
  obtain ⟨hA, -, -, -, hW⟩ := h
  obtain ⟨S, Nd, hT, hTS, hD⟩ := hs
  obtain ⟨S', Nd', -, hT', -⟩ := hW S Nd hT hTS hD
  exact ⟨hA, S', (worldTyped_iff_with post S').2 ⟨Nd', hT'⟩⟩

/-- Every `WorldStep` is a `WorldStepIn T` for any `T` (proved). -/
theorem WorldStep.stepIn {T : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Nat}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {F : Type} {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (h : WorldStep R gw keep Q s r post) : WorldStepIn T R gw keep Q s r post := by
  obtain ⟨hA, hH, hG, hK, hW⟩ := h
  exact ⟨hA, hH, hG, hK, fun S Nd hT _ hD => hW S Nd hT hD⟩

/-- A world step from a state typed with `R` avoided ends in `WorldOK` (proved). -/
theorem WorldStep.worldOK {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {F : Type} {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (h : WorldStep R gw keep Q s r post)
    (hs : ∃ S Nd, WorldTypedWith s S Nd ∧ IvlsDisj (R s) (worldTypedIvls s S Nd)) :
    WorldOK post := by
  obtain ⟨hA, -, -, -, hW⟩ := h
  obtain ⟨S, Nd, hT, hD⟩ := hs
  obtain ⟨S', Nd', -, hT', -⟩ := hW S Nd hT hD
  exact ⟨hA, S', (worldTyped_iff_with post S').2 ⟨Nd', hT'⟩⟩

/-- With no output region, a world step keeps `WorldOK` (proved). -/
theorem WorldStep.worldOK_nil {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {F : Type} {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (h : WorldStep (fun _ => []) gw keep Q s r post) (hs : WorldOK s) : WorldOK post := by
  obtain ⟨-, S, hS⟩ := hs
  obtain ⟨Nd, hT⟩ := (worldTyped_iff_with s S).1 hS
  exact h.worldOK ⟨S, Nd, hT, fun o ho => by simp at ho⟩

/-- A relational world contract without output region implies the revision-6 shape (proved), so
the proved compositions that only need `WorldOK` after the call keep their proofs. -/
theorem WorldKeeps.keepsOn {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop} {fname : MlS}
    (h : WorldKeeps WorldOK (fun _ => []) gw keep Q fname) : KeepsOn WorldOK WorldOK fname := by
  obtain ⟨params, body, ret, hlook, hb⟩ := h
  exact ⟨params, body, ret, hlook, fun s hc hW hnt hr => (hb s hc hW hnt hr).worldOK_nil hW⟩

/-- `EvmInv` with an output region `R` that avoids the typed world, the persistent tries and every
frame block (revision 7: the EVM-tier callees that write a caller buffer, `u256_to_be32` into
`evm_key_buf`). -/
def EvmAvoids (R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ ∃ S, EvmInvAt s S ∧ ∃ Nd, TriesTypedWith s S Nd ∧
    IvlsDisj (R s) (worldTypedIvls s S Nd ++ ((evmChain s).map (frameObjects s)).flatten)

/-- The EVM-tier relational step (revision 7, round-4 Gemini item 1(b)): `EvmInv` again, the heap
only grows, the globals outside `gw` are unchanged (in particular `ev` and `cur_cont` for every
callee that does not assign them) and the frame chain `evmChain` is the same list of (record,
continuation) pairs. None of these callees opens or pops a frame (`frame_open`, `finish_child` have
their own contracts). -/
def EvmStep (gw : List String) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Prop :=
  fun s post => EvmInv post ∧ globN s "heap_ptr" ≤ globN post "heap_ptr" ∧ GlobalsKept gw s post ∧
    evmChain post = evmChain s

def EvmKeeps (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop) (gw : List String)
    (fname : MlS) : Prop :=
  FunSpec P (fun s r post => Resumes r → EvmStep gw s post) fname

/-- The revision-6 shape, from an `EvmInv` entry (proved). -/
theorem EvmKeeps.keepsOn {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {gw : List String} {fname : MlS} (h : EvmKeeps P gw fname) : KeepsOn P EvmInv fname := by
  obtain ⟨params, body, ret, hlook, hb⟩ := h
  exact ⟨params, body, ret, hlook, fun s hc hP hnt hr => (hb s hc hP hnt hr).1⟩

/-- The intervals of a trie object `m` with node set `Nm`. -/
def mptObjIvls {F : Type} (s : PanSemStateFiniteExact 64 F) (Nm : List Nat) (m : Nat) : List Ivl :=
  (m, 16) :: nodeExtents s Nm

/-- The relational step of `mpt_set(m, …)` / `mpt_root(m, out)` (revision 7): `WorldStep`'s
clauses, and in addition the trie object `m` stays typed in the SAME world `S' ⊇ S`, away from the
persistent tries, its intervals grow only into fresh heap, and its records may change (they are the
function's work). The callers `build_mpt_indexed`, `compute_state_root` call `mpt_set` in a loop on
one object and `mpt_root` on it afterwards. Revision 8 (round-5 Fable non-blocking): the object's
node extents are disjoint from the persistent tries' at entry and exit. -/
def MptObjStep (R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl) (gw : List String)
    (keep : List (String × List Nat)) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Prop :=
  fun s post =>
    ArenaReady post ∧ globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
    GlobalsKept gw s post ∧ RecordsKept R keep s post ∧
    ∀ S Nd Nm, WorldTypedWith s S Nd → MptObjInWith s S Nm (locN s "m") →
      IvlsDisj ((locN s "m", 16) :: R s ++ nodeExtents s Nm) (nodeExtents s Nd) →
      IvlsDisj (R s) (worldTypedIvls s S Nd ++ mptObjIvls s Nm (locN s "m")) →
      ∃ S' Nd' Nm', (∀ t ∈ S, t ∈ S') ∧ WorldTypedWith post S' Nd' ∧
        MptObjInWith post S' Nm' (locN s "m") ∧
        IvlsDisj ((locN s "m", 16) :: nodeExtents post Nm') (nodeExtents post Nd') ∧
        OwnedGrows s post (worldOwned s S Nd ++ mptObjIvls s Nm (locN s "m"))
          (worldOwned post S' Nd' ++ mptObjIvls post Nm' (locN s "m")) ∧
        FrameOutside s post
          (worldOwned s S Nd ++ mptObjIvls s Nm (locN s "m") ++ R s ++ [freeGap s]) (heapFree s)

def MptKeeps (R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl) (gw : List String)
    (keep : List (String × List Nat)) (fname : MlS) : Prop :=
  FunSpec MptObjReady (fun s r post => Resumes r → MptObjStep R gw keep s post) fname

/-! ### Constructor return typing (revision 7, round-4 Gemini item 1(c)) -/

/-- `[p, p + round8 n)` is heap allocated between `s` and `post`, `p` aligned, all words. -/
def FreshBlock {F : Type} (s post : PanSemStateFiniteExact 64 F) (p n : Nat) : Prop :=
  p % 8 = 0 ∧ Inside (p, (n + 7) / 8 * 8) (globN s "heap_ptr") (globN post "heap_ptr") ∧
    WordsOK post (p, (n + 7) / 8 * 8)

/-- A normal return is a word `w` with `Q s post w`. -/
def RetWord (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Nat →
    Prop) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop :=
  fun s r post => ∀ v, r = some (.returned v) → ∃ w : BitVec 64, v = .val (.word w) ∧ Q s post w.toNat

def Returns (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Nat → Prop)
    (fname : MlS) : Prop :=
  FunSpec P (RetWord Q) fname

/-- `mpt_from_witness`'s extra (revision 7): the returned trie object is a fresh 16-byte block
with a fresh typed node set, placed in the exit world `S'` (`MptObjInWith`) and away from its
persistent tries. -/
def RetMptObj : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
    PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop :=
  fun s r post S' Nd' => ∀ v, r = some (.returned v) → ∃ w : BitVec 64, v = .val (.word w) ∧
    ∃ Nm, MptObjInWith post S' Nm w.toNat ∧ IvlsDisj (mptObjIvls post Nm w.toNat) (nodeExtents post Nd') ∧
      ∀ o ∈ mptObjIvls post Nm w.toNat, o = (0, 0) ∨
        Inside o (globN s "heap_ptr") (globN post "heap_ptr")

/-- A constructor's extra (revision 8, round-5 Astra item 4, Gemini suggestion): the returned
object's intervals `B s post w` are disjoint from the EXIT world `worldOwned post S' Nd'`. Fresh heap
alone does not give this: `OwnedGrows` lets the world grow into the heap allocated during the call,
so a constructor could attach its fresh block to a trie node (`n+32 := p`) and return it, and the
caller's own stores into the block (`te+0 := sender`) then overwrote the world. -/
def RetAvoids (B : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Nat →
    List Ivl) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop :=
  fun s r post S' Nd' => ∀ v, r = some (.returned v) → ∃ w : BitVec 64, v = .val (.word w) ∧
    IvlsDisj (B s post w.toNat) (worldOwned post S' Nd')

/-- `RetAvoids` when the entry satisfies `C` (revision 8): `lst_new` with a non-wrapping element
array, `htab_copy` of a well-formed allocated table (a garbage header gives a meaningless
footprint). -/
def RetAvoidsIf (C : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (B : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Nat →
      List Ivl) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop :=
  fun s r post S' Nd' => C s → RetAvoids B s r post S' Nd'

/-- `lst_push(l, 8)`'s extra (revision 8, round-5 Astra item 6): the returned element slot is an
aligned word inside the list's backing array at exit (`lst_push` 13840 returns
`load(l) + 8·n` after raising the length to `n + 1 ≤ capacity`). The backing array of `bo+40`/`bo+72`
is a fixed object (`blockOutObjects`) whose contents `WorldTyped` does not read, so the caller's store
of a log pointer through the slot keeps the typing, and the slot is disjoint from every table, trie
node and other fixed object. An identity transition returning an existing table header satisfied
the revision-7 contract. -/
def RetListSlot : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
    PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop :=
  fun s r post _ _ => ∀ v, r = some (.returned v) → ∃ w : BitVec 64, v = .val (.word w) ∧
    w.toNat % 8 = 0 ∧ Inside (w.toNat, 8) (memW post (locN s "l"))
      (memW post (locN s "l") + 8 * memW post (locN s "l" + 16))

/-- `bal_remove_change(addr, which, esz, idx)` entry (revision 8, round-5 Astra item 2): the list
selector and element size are one of the three BAL change lists (`update_builder_from_tx` passes
`(16, 40)`, `(24, 16)`, `(32, 24)`, AST 14270-14280). With `which = 40` it read the unowned word
`ad+40` as a list and removed an element through it. -/
def BalChangeArg : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => WorldOK s ∧ ((locN s "which" = 16 ∧ locN s "esz" = 40) ∨
    (locN s "which" = 24 ∧ locN s "esz" = 16) ∨ (locN s "which" = 32 ∧ locN s "esz" = 24))

/-- `[p, p + round8 n)` is scratch allocated between `s` and `post` (revision 8): aligned, above
the frame-memory pointer, inside `[scratch_ptr post, scratch_ptr s)`, all words. -/
def FreshScratch {F : Type} (s post : PanSemStateFiniteExact 64 F) (p n : Nat) : Prop :=
  p % 8 = 0 ∧ globN s "frame_mem_ptr" ≤ p ∧
    Inside (p, (n + 7) / 8 * 8) (globN post "scratch_ptr") (globN s "scratch_ptr") ∧
    WordsOK post (p, (n + 7) / 8 * 8)

/-- `_decode_step(db, p, n)` (revision 8, round-5 Astra item 7, Gemini suggestion): a normal return
`<1, rec>` pushed a fresh 88-byte scratch record (`scratch_alloc(88)`, AST 10110) tagged `1`
(extension) or `2` (branch, slot counter `+32` and occupancy `+40` zero). With the write frame
`ww__decode_step` (memory free at entry only; `scratch_ptr` never rises), the records already on
`_decode_witness_node_body`'s stack, their links and counters, are untouched, and each push lowers
`scratch_ptr` by at least 88: the revision-7 `KeepsOn ArenaReady ArenaReady` allowed returning the
same record repeatedly and overwriting the saved links. -/
def PushesFrame (fname : MlS) : Prop :=
  FunSpec ArenaReady (fun s r post => ∀ v, r = some (.returned v) → ∃ a b : BitVec 64,
    v = .rStruct [.val (.word a), .val (.word b)] ∧ (a.toNat ≠ 0 →
      FreshScratch s post b.toNat 88 ∧ (memW post (b.toNat + 8) = 1 ∨
        (memW post (b.toNat + 8) = 2 ∧ memW post (b.toNat + 32) = 0 ∧
          memW post (b.toNat + 40) = 0)))) fname

/-- `node_invalidate(nd)` (revision 8, round-5 Astra item 7, Gemini suggestion; AST 10061): on a
typed node (or `0`, which errors) it zeroes the three cache words `nd+8`, `nd+16`, `nd+24` and
changes nothing else (globals, other memory). So a second call on the same node is the identity,
which `_mpt_insert_node`'s stationary argument on a self-looping empty extension needs; the
`NodeFn` contract alone allowed changes across node records and the free scratch gap. -/
def InvalidatesCache (fname : MlS) : Prop :=
  FunSpec (NodeArgs ["nd"] (fun _ _ => True)) (fun s r post => Resumes r →
    post = { s with
      memory := fun a => if a = BitVec.ofNat 64 (locN s "nd" + 8) ∨ a = BitVec.ofNat 64 (locN s "nd" + 16) ∨
          a = BitVec.ofNat 64 (locN s "nd" + 24) then HolWordLab.word 0 else s.memory a,
      locals := post.locals, clock := post.clock }) fname

/-- `requests_append`'s extra (revision 7, round-4 Gemini item 1(a)): the request count `bo+64`
goes up by exactly one. -/
def ReqCountInc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
    PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop :=
  fun s _ post _ _ => memW post (globN s "bo" + 64) = memW s (globN s "bo" + 64) + 1

/-- The host-input cells `run_attempt` reads the transaction count through: `si+0 = pl` and
`pl+40 = ntx` (revision 7). -/
def inputCells {F : Type} (s : PanSemStateFiniteExact 64 F) (si : Nat) : List Ivl :=
  [(si, 8), (memW s si + 40, 8)]

/-- `decode_host_input`'s extra (revision 7): the returned input record and its payload record are
fresh heap words. Revision 8 (round-5 Astra items 4 and 8, Gemini suggestion): they are disjoint
from the EXIT world `worldOwned post S' Nd'` (fresh heap alone does not say so, since `OwnedGrows`
lets the world grow into fresh heap), and the transaction count `pl+40` is below `2^63`
(`decode_payload`'s `ssz_split_var_list` bounds it; `run_attempt` compares it with SIGNED `<`, so
`ntx = 2^63` ran zero iterations and left `16·ntx + 16` wrapping). -/
def RetInput : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
    PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop :=
  fun s r post S' Nd' => ∀ v, r = some (.returned v) → ∃ w : BitVec 64, v = .val (.word w) ∧
    (∀ i ∈ inputCells post w.toNat, i.1 % 8 = 0 ∧
      Inside i (globN s "heap_ptr") (globN post "heap_ptr") ∧ WordsOK post i) ∧
    IvlsDisj (inputCells post w.toNat) (worldOwned post S' Nd') ∧
    memW post (memW post w.toNat + 40) < 2 ^ 63

/-- Guard of `verify_stateless_new_payload`, `attempt_l*`, `run_attempt` (revision 7): `WorldOK`,
and the input cells are allocated words outside the world, for one typing. `run_attempt` checks
every transaction slot `txs + 16 i + 8, i < ntx` by a `load` (33778), which errors unless
`16·ntx + 16 < 2^64` (a full cycle of `16 i mod 2^64` leaves the memory domain), and
`execute_block`'s guard `BlockReady` needs that bound; it reads `ntx` again through `si+0`, `pl+40`
at `execute_block`'s entry, so those two cells must survive the calls in between (`payload_header`,
`header_hash`, `validate_header`, …), which `WorldStep` guarantees for memory outside the world.
Revision 8 (round-5 Astra item 8): `ntx < 2^63`, so `run_attempt`'s signed loop test `i < ntx`
counts `ntx` iterations (with `ntx = 2^63` it ran none and `BlockReady` failed). -/
def InputAt {F : Type} (s : PanSemStateFiniteExact 64 F) (si : Nat) : Prop :=
  ArenaReady s ∧ ∃ S Nd, WorldTypedWith s S Nd ∧
    (∀ i ∈ inputCells s si, Inside i sourceBase (globN s "heap_ptr") ∧ WordsOK s i) ∧
    IvlsDisj (inputCells s si) (worldOwned s S Nd) ∧
    memW s (memW s si + 40) < 2 ^ 63

def InputReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => InputAt s (locN s "si")

theorem inputReady_worldOK {F : Type} (s : PanSemStateFiniteExact 64 F) (h : InputReady s) :
    WorldOK s := by
  obtain ⟨hA, S, Nd, hT, -⟩ := h
  exact ⟨hA, S, (worldTyped_iff_with s S).2 ⟨Nd, hT⟩⟩

theorem inputReady_guestInv {F : Type} (s : PanSemStateFiniteExact 64 F) (h : InputReady s) :
    GuestInv s := h.1.1

theorem arenaReady_guestInv {F : Type} (s : PanSemStateFiniteExact 64 F) (h : ArenaReady s) :
    GuestInv s := h.1

theorem inputAt_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k si : Nat) :
    InputAt { s with locals := locals, clock := k } si ↔ InputAt s si := by
  simp only [InputAt, WorldTypedWith, tablesTyped_with_locals, arenaReady_with_locals]
  exact Iff.rfl

theorem localsOnly_inputReady : LocalsOnly ["si"] InputReady := by
  intro F s locals k hl hP
  have ht := locN_congr s locals k "si" (hl "si" (by simp))
  show InputAt _ _
  rw [ht]
  exact (inputAt_with_locals s locals k _).2 hP

/-- The callee of a one-parameter function called with the caller's local of the same name sees
that local's value (proved). -/
theorem callee_param_one {F : Type} (state : PanSemStateFiniteExact 64 F) (fname pk : MlS)
    (sk : ShapeHOL) (body : ProgHOL 64) (ret : ShapeHOL)
    (hl : state.code.lookup fname = some ([(pk, sk)], body, ret))
    (values : List (ValueHOL 64)) (body' : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL)
    (hargs : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local pk] = some values)
    (hlook : lookupCodeHOLFinite state.code.lookup fname values = some (body', callee, ret')) :
    callee.lookup pk = state.locals.lookup pk := by
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
    rcases hv : state.locals.lookup pk with _ | v
    · rw [hv] at hargs; cases hargs
    · rw [hv] at hargs
      cases hargs
      split at raw
      · have rawEq := Option.some.inj raw
        rcases Prod.mk.inj rawEq with ⟨-, hrest2⟩
        rcases Prod.mk.inj hrest2 with ⟨hloc, -⟩
        subst hloc
        simp
      · cases raw

/-- A call `f(si)` to a function whose only parameter is `si` keeps `InputReady` (proved): the
attempt chain `verify_stateless_new_payload → attempt_l7 → … → attempt_l1 → run_attempt`. -/
theorem callEntryOn_inputReady {fname : MlS} {e : List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL}
    (hl : originalRuntimeCode.lookup fname = some e) (hp : e.1 = [(ofString "si", .one)]) :
    CallEntryOn InputReady InputReady fname [.var .local (ofString "si")] := by
  obtain ⟨ps, b, r⟩ := e
  dsimp only at hp
  subst hp
  intro F state values body' callee ret' hcode hP hargs hlook
  have hc := callee_param_one state fname (ofString "si") .one b r (by rw [hcode]; exact hl) values
    body' callee ret' hargs hlook
  have hsi : locN (callEntryStateHOLFinite state callee) "si" = locN state "si" := by
    simp only [locN, callEntryStateHOLFinite, hc]
  show InputAt (callEntryStateHOLFinite state callee) (locN (callEntryStateHOLFinite state callee) "si")
  rw [hsi]
  exact (inputAt_with_locals state callee (state.clock - 1) _).2 hP

/-- The callee of a four-parameter function called with the caller's locals of the same names sees
those locals' values (revision 8, proved; W6 for `MptReady`). -/
theorem callee_param_four {F : Type} (state : PanSemStateFiniteExact 64 F) (fname a b c d : MlS)
    (sa sb sc sd : ShapeHOL) (body : ProgHOL 64) (ret : ShapeHOL)
    (hl : state.code.lookup fname = some ([(a, sa), (b, sb), (c, sc), (d, sd)], body, ret))
    (values : List (ValueHOL 64)) (body' : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL)
    (hargs : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local a, .var .local b, .var .local c, .var .local d] = some values)
    (hlook : lookupCodeHOLFinite state.code.lookup fname values = some (body', callee, ret')) :
    ∀ n ∈ [a, b, c, d], callee.lookup n = state.locals.lookup n := by
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
    rcases hva : state.locals.lookup a with _ | va <;>
    rcases hvb : state.locals.lookup b with _ | vb <;>
    rcases hvc : state.locals.lookup c with _ | vc <;>
    rcases hvd : state.locals.lookup d with _ | vd <;>
      simp only [hva, hvb, hvc, hvd] at hargs <;> try cases hargs
    split at raw
    · rename_i hcond
      have rawEq := Option.some.inj raw
      rcases Prod.mk.inj rawEq with ⟨-, hrest2⟩
      rcases Prod.mk.inj hrest2 with ⟨hloc, -⟩
      subst hloc
      obtain ⟨hnd, -, -⟩ := hcond
      simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
        not_or, List.not_mem_nil] at hnd
      intro n hn
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl | rfl | rfl <;>
        simp_all [List.zip, List.foldl, Ne.symm]
    · cases raw

/-- A call `f(node, key, klen, level)` to a function with exactly those parameters keeps `MptReady`
(revision 8, proved): `_mpt_delete_node → _mpt_delete_node_body`. -/
theorem callEntryOn_mptReady {fname : MlS} {e : List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL}
    (hl : originalRuntimeCode.lookup fname = some e)
    (hp : e.1 = [(ofString "node", .one), (ofString "key", .one), (ofString "klen", .one),
      (ofString "level", .one)]) :
    CallEntryOn MptReady MptReady fname [.var .local (ofString "node"), .var .local (ofString "key"),
      .var .local (ofString "klen"), .var .local (ofString "level")] := by
  obtain ⟨ps, b, r⟩ := e
  dsimp only at hp
  subst hp
  intro F state values body' callee ret' hcode hP hargs hlook
  have hc := callee_param_four state fname _ _ _ _ .one .one .one .one b r (by rw [hcode]; exact hl)
    values body' callee ret' hargs hlook
  exact localsOnly_mptReady state callee (state.clock - 1)
    (fun n hn => hc (ofString n) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn ⊢
      rcases hn with rfl | rfl | rfl | rfl <;> simp)) hP

/-- Value contract (revision 7): the function resumes its caller only if its table parameter `x` is
nonzero (its first action loads through it, and address `0` is outside the memory domain).
`get_storage` calls `htab_set(load(ts + 24), …)` and then the guarded `ws_get_storage`; `RootIn`
allows the slot to be `0`, where `htab_set_spec` does not apply. -/
def ArgNonNull (x : String) (fname : MlS) : Prop :=
  FunSpec GuestInv (fun s r _ => Resumes r → locN s x ≠ 0) fname

/-- Value contract (revision 7): the function resumes its caller only if the region `R s` (when
non-empty) lies in the memory domain: it loads or stores through all of it, and an access outside
`[sourceBase, heapEnd)` errors. The walks of `process_transaction` (`memcpy` into `al_keys`) and
`payload_header` (`encode_withdrawal_rlp(wd + 44 i)`) use it to show that a loop whose count was read
from memory exits normally only when the count is small, so the arrays sized by it did not wrap. -/
def ResumesInDomain (R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Ivl) (fname : MlS) : Prop :=
  FunSpec GuestInv (fun s r _ => Resumes r → 0 < (R s).2 → Inside (R s) sourceBase heapEnd) fname

/-- `lst_push(l, esz)` at a world-tier site (revision 7): `process_transaction` pushes onto the
block's log list `bo+40` and receipt-log list `bo+72` (33398, 33418), world objects
(`blockOutObjects`) with 8-byte elements. -/
def BoListArg : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => WorldOK s ∧ globN s "bo" ≠ 0 ∧
    (locN s "l" = memW s (globN s "bo" + 40) ∨ locN s "l" = memW s (globN s "bo" + 72)) ∧
    locN s "esz" = 8

/-- Value contract (revision 7, `execute_block` needs `bo+64 = 0` after `memzero(bo, 88)`): a
normal return of `memzero(dst, n)` leaves every aligned word inside `[dst, dst + n)` zero. -/
def ZeroFills (fname : MlS) : Prop :=
  FunSpec ArenaReady (fun s r post => ∀ v, r = some (.returned v) → ∀ a, locN s "dst" ≤ a →
    a + 8 ≤ locN s "dst" + locN s "n" → a % 8 = 0 → memW post a = 0) fname

/-- Value contract (revision 7): `validate_transaction` returns its intrinsic cost triple with
regular part at most `2^24` (`TxErr 63` otherwise, AST 12667). `process_transaction` computes the
message gas `min(2^24 − regular, gas − intrinsic) ≤ 2^24`, which `MsgReady` bounds by `2^63`. -/
def RetIntrinsic (fname : MlS) : Prop :=
  FunSpec GuestInv (fun _ r _ => ∀ v, r = some (.returned v) →
    ∃ a b c : BitVec 64, v = .rStruct [.val (.word a), .val (.word b), .val (.word c)] ∧
      a.toNat ≤ 16777216) fname

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
  refine ⟨localsFree_worldOK s locals k hP.1, hP.2.1, hP.2.2.1, hP.2.2.2.1, ?_⟩
  show locN { s with locals := locals, clock := k } "index" < memW s (globN s "bo" + 80)
  rw [ht]; exact hP.2.2.2.2

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

/-! ### Direct callees, read off the AST (revision 6, round-4 Astra item 8)

Each `GBody.«f»` below is an obligation about the body of the single function `f`. Its
hypotheses are the bound of each direct callee of `f` and the contract of each callee at a
guard-carrying call site; `«callees_f»` checks, by `decide` on the literal AST, that the direct
callees of `f` are exactly the functions whose bounds are listed. -/

/-- Every function named by a `call` or `decCall` in a body (exception handlers included). -/
def progCallees : Prog (BitVec 64) → List String
  | .dec _ _ _ b => progCallees b
  | .seq a b => progCallees a ++ progCallees b
  | .ite _ a b => progCallees a ++ progCallees b
  | .while _ b => progCallees b
  | .call (some (_, some (_, _, h))) g _ => g :: progCallees h
  | .call _ g _ => [g]
  | .decCall _ _ g _ b => g :: progCallees b
  | _ => []

def fnBody : Decl (BitVec 64) → Prog (BitVec 64)
  | .function fd => fd.body
  | _ => .skip

/-- The two lists name the same set of functions. -/
def sameNames (l m : List String) : Bool := l.all (· ∈ m) && m.all (· ∈ l)

/-! ### Guard-carrying `seq` from the Hoare layer (revision 6, round-4 Astra item 8) -/

/-- Guarded `seq` that needs the guard after the first part only when it falls through (a
normal `none` result), stated as a Hoare triple. `seq_on` asks for preservation on every outcome,
which fails for calls (a trapped callee leaves an arbitrary state). -/
theorem TerminatingProgBoundedOn.seq_hoare
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {first second : ProgHOL 64} {a b : Nat}
    (h1 : TerminatingProgBoundedOn P first a) (hp : Hoare P first (fun r t => r = none → P t))
    (h2 : TerminatingProgBoundedOn P second b) :
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

theorem return_ne_none {F : Type} (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) :
    (evaluateHOLFiniteState s (.return e)).1 ≠ none := by
  rw [evaluateHOLFiniteState_return]
  split
  · simp
  · split <;> simp

theorem clock_skip {F : Type} (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s .skip).2.clock = s.clock := by simp

/-- An early-return guard clause `if c then return e` falls through only from the unchanged
state. -/
theorem Hoare.ite_return_skip {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (cond e : ExpHOL 64) : Hoare P (.ite cond (.return e) .skip) (fun r t => r = none → P t) :=
  Hoare.ite ⟨fun s _ _ _ h => absurd h (return_ne_none s e)⟩ (Hoare.skip fun _ h _ => h.1)
    (fun _ _ h => absurd h (by simp))

/-- A handler-free call without destination to a callee that keeps the locals-free guard `W`
falls through only into a `W` state. -/
theorem Hoare.call_keeps {W : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hW : LocalsFree W) {fname : MlS} (hk : KeepsOn W W fname) (arguments : List (ExpHOL 64)) :
    Hoare W (.call (some (none, none)) fname arguments) (fun r t => r = none → W t) :=
  Hoare.call0 hk (callEntryOn_of_localsFree hW _ _)
    (fun s _ post v _ _ hq _ => hW post s.locals post.clock (hq (Or.inl ⟨v, rfl⟩)))
    (fun _ _ hr _ h => absurd h hr)

/-- `if c then (call g) ` with `g` keeping `W`, as a fall-through triple. -/
theorem Hoare.ite_call_keeps {W : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hW : LocalsFree W) {fname : MlS} (hk : KeepsOn W W fname) (cond : ExpHOL 64)
    (arguments : List (ExpHOL 64)) :
    Hoare W (.ite cond (.call (some (none, none)) fname arguments) .skip)
      (fun r t => r = none → W t) :=
  Hoare.ite (Hoare.mono (Hoare.call_keeps hW hk arguments) (fun _ h => h.1))
    (Hoare.skip fun _ h _ => h.1) (fun _ _ h => absurd h (by simp))

theorem clock_store {F : Type} (s : PanSemStateFiniteExact 64 F) (a v : ExpHOL 64) :
    (evaluateHOLFiniteState s (.store a v)).2.clock = s.clock := by
  rw [evaluateHOLFiniteState_store]
  repeat' split
  all_goals (try dsimp only)

/-! ### World steps in the Hoare layer (revision 7) -/

/-- A `decCall` to a callee keeping the locals-free guard `W` resumes in `W` (proved). -/
theorem KeepsOn.resumeOn {W : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hW : LocalsFree W) {fname : MlS} (h : KeepsOn W W fname) (name : MlS)
    (arguments : List (ExpHOL 64)) : DecCallResumeOn W W name fname arguments := by
  obtain ⟨params, body', ret', hlook, hb⟩ := h
  intro F state values body callee ret value post hcode hP _ hl hrun
  have hsame := lookupCodeHOLFinite_installed_body state.code.lookup fname params body' body
    ret' ret values callee (by rw [hcode]; exact hlook) hl
  subst hsame
  have hq := hb (callEntryStateHOLFinite state callee) hcode (hW state _ _ hP)
    (by rw [hrun]; simp) (by rw [hrun]; exact Or.inl ⟨value, rfl⟩)
  rw [hrun] at hq
  have := hW post (state.locals.update (name, value)) post.clock hq
  simpa [setVarHOLFinite] using this

theorem raise_ne_none {F : Type} (s : PanSemStateFiniteExact 64 F) (n : MlS) (e : ExpHOL 64) :
    (evaluateHOLFiniteState s (.raise n e)).1 ≠ none := by
  rw [evaluateHOLFiniteState_raise]
  repeat' split
  all_goals (try simp)
  all_goals (split_ifs <;> simp)

/-- A guard clause `if c then raise …` falls through only from the unchanged state (proved). -/
theorem Hoare.ite_raise_skip {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (cond : ExpHOL 64) (n : MlS) (e : ExpHOL 64) :
    Hoare P (.ite cond (.raise n e) .skip) (fun r t => r = none → P t) :=
  Hoare.ite ⟨fun s _ _ _ h => absurd h (raise_ne_none s n e)⟩ (Hoare.skip fun _ h _ => h.1)
    (fun _ _ h => absurd h (by simp))
