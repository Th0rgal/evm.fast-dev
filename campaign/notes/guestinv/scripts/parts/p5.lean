
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
changes (round-2 Astra item 2: revision 2 intersected the two frames). -/
def HtabNewExit : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
    PanSemStateFiniteExact 64 F → Prop :=
  fun s r post => ∀ v, r = some (.returned v) → ∃ w : BitVec 64, v = .val (.word w) ∧
    ArenaReady post ∧ HtabWF post w.toNat ∧ hdr post w.toNat 3 = 0 ∧
    (∀ i ∈ htabFootprint post w.toNat, Allocated post i ∧
      (Inside i (globN s "heap_ptr") (globN post "heap_ptr") ∨
        Inside i (globN post "scratch_ptr") (globN s "scratch_ptr"))) ∧
    FrameOutside s post
      [(globN post "scratch_ptr", globN s "scratch_ptr" - globN post "scratch_ptr")]
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr")

/-- Entry of `htab_new` / `htab_new_scratch` (round-2 Fable item 1, Astra item 3): separated
arenas, a key length and a capacity from the 32 literal call sites. `htab_new` checks neither:
`key_len = 0` breaks `1 ≤ klen`, `61` breaks `klen ≤ maxKeyLen`, `2^64 - 3` wraps the stride;
`cap = 2^64 - 1` wraps `(ncap + 1) * stride`. -/
def HtabNewReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ locN s "key_len" ∈ htabKeyLens ∧ locN s "cap" ∈ htabCaps

theorem htab_new_spec : FunSpec HtabNewReady HtabNewExit (ofString "htab_new") := by sorry
theorem htab_new_scratch_spec :
    FunSpec HtabNewReady HtabNewExit (ofString "htab_new_scratch") := by sorry

/-! ### MPT update contracts (`_mpt_insert_node`, `_mpt_delete_node_body`) -/

/-- Entry of the two MPT update functions: separated arenas and a typed trie below the `node`
parameter. -/
def MptReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ ∃ Nd, NodeHeap s Nd ∧ RootIn Nd (locN s "node")

/-- `mpt_set(m, …)`: the 16-byte trie object `m` (`mpt_new` 10446: `+0` root node) is allocated
and its root is typed. -/
def MptObjReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ Allocated s (locN s "m", 16) ∧ WordsOK s (locN s "m", 16) ∧
    ∃ Nd, NodeHeap s Nd ∧ RootIn Nd (memW s (locN s "m")) ∧
      ∀ n ∈ Nd, Disj (n, 176) (locN s "m", 16)

/-- Exit: the returned root is typed in the new node heap, which extends the old one by fresh
heap records; old memory outside the old nodes and fresh heap/scratch is unchanged. -/
def MptExit : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
    PanSemStateFiniteExact 64 F → Prop :=
  fun s r post => ∀ v, r = some (.returned v) → ∃ w : BitVec 64, v = .val (.word w) ∧
    ArenaReady post ∧ globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
    ∃ Nd Nd', NodeHeap s Nd ∧ RootIn Nd (locN s "node") ∧ NodeHeap post Nd' ∧
      RootIn Nd' w.toNat ∧
      FrameOutside s post (Nd.map fun n => (n, 176))
        (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr")

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

/-- Glue: the four frame contracts compose to `run_frames_step` (the loop body only adds loads,
local assignments and the outermost-exit assignments of `ev`/`cur_cont`/`go`). -/
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
      locN (evaluateHOLFiniteState (decClockHOLFinite s) b).2 "go" = 0 := by sorry

/-- One continuing iteration of the `run_frames` loop strictly lowers `evmPot` and keeps
`EvmInv`, or ends the loop (`go := 0` after the outermost frame). Proved from the four contract
leaves and the glue. -/
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

/-! ### Guards of the guarded bound leaves -/

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

theorem localsFree_finishReady : LocalsFree FinishReady := by
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
  simp only [MptObjReady, arenaReady_with_locals] at hP ⊢
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
