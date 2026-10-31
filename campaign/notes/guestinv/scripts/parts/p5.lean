
/-! ## 7. Guarded tier: contracts and leaves

The six loops without an arbitrary-memory measure (`run_frames`, `htab_truncate`,
`_decode_witness_node_body`, `_mpt_insert_node`, `_mpt_delete_node_body` ×2) and every function
that (transitively) calls one of them. Each such function has a bound leaf under an explicit
guard (`guardedLeaves` below and DESIGN.md §6); the memory facts those leaves need at their
guarded call sites are the contracts of this section, each a separate leaf. -/

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
theorem htab_truncate_spec :
    FunSpec HtabArgWF (OnReturn HtabExit) (ofString "htab_truncate") := by sorry
theorem htab_union_into_spec :
    FunSpec UnionArgWF (OnReturn UnionExit) (ofString "htab_union_into") := by sorry

/-- `htab_new` / `htab_new_scratch` return a well-formed empty table whose footprint is freshly
allocated (heap resp. scratch); nothing else in memory changes. -/
def HtabNewExit : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
    PanSemStateFiniteExact 64 F → Prop :=
  fun s r post => ∀ v, r = some (.returned v) → ∃ w : BitVec 64, v = .val (.word w) ∧
    ArenaReady post ∧ HtabWF post w.toNat ∧ hdr post w.toNat 3 = 0 ∧
    (∀ i ∈ htabFootprint post w.toNat, Allocated post i ∧
      (Inside i (globN s "heap_ptr") (globN post "heap_ptr") ∨
        Inside i (globN post "scratch_ptr") (globN s "scratch_ptr"))) ∧
    FrameOutside s post [] (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") ∧
    FrameOutside s post [] (globN post "scratch_ptr", globN s "scratch_ptr" - globN post "scratch_ptr")

theorem htab_new_spec : FunSpec ArenaReady HtabNewExit (ofString "htab_new") := by sorry
theorem htab_new_scratch_spec :
    FunSpec ArenaReady HtabNewExit (ofString "htab_new_scratch") := by sorry

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
