import InitECandidate.Solver.Wave8GuestInv.ContractParts.C10
import InitECandidate.Solver.Wave8GuestInv.Deliveries.GBODY_RUNFRAMES_SOL.Base
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptCache
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

structure MptInsertCallees : Prop where
  fb__insert_into_leaf : TerminatingFunBoundedOn GuestInv (ofString "_insert_into_leaf") K.«_insert_into_leaf»
  fb__split_extension : TerminatingFunBoundedOn GuestInv (ofString "_split_extension") K.«_split_extension»
  fb_common_prefix_length : TerminatingFunBoundedOn GuestInv (ofString "common_prefix_length") K.«common_prefix_length»
  fb_mpt_fail : TerminatingFunBoundedOn GuestInv (ofString "mpt_fail") K.«mpt_fail»
  fb_node_invalidate : TerminatingFunBoundedOn GuestInv (ofString "node_invalidate") K.«node_invalidate»
  fb_node_new_ext : TerminatingFunBoundedOn GuestInv (ofString "node_new_ext") K.«node_new_ext»
  fb_node_new_leaf : TerminatingFunBoundedOn GuestInv (ofString "node_new_leaf") K.«node_new_leaf»
  nf__insert_into_leaf : NodeFn ["node"]
    (fun s Nd =>
      NodeKind s Nd "node" 1 ∧ KeyIn s Nd (locN s "rk") (locN s "rl"))
    (ofString "_insert_into_leaf")
  nf__split_extension : NodeFn ["node"]
    (fun s Nd =>
      NodeKind s Nd "node" 2 ∧ KeyIn s Nd (locN s "rk") (locN s "rl") ∧
      locN s "pl" < memW s (locN s "node" + 40) ∧ locN s "pl" ≤ locN s "rl")
    (ofString "_split_extension")
  ro_common_prefix_length : ReadOnlyFn (ofString "common_prefix_length")
  rv_common_prefix_length : RetLe (fun s => min (locN s "al") (locN s "bl")) (ofString "common_prefix_length")
  ro_mpt_fail : ReadOnlyFn (ofString "mpt_fail")
  nf_node_invalidate : NodeFn ["nd"]
    (fun _ _ => True)
    (ofString "node_invalidate")
  iz_node_invalidate : InvalidatesCache (ofString "node_invalidate")
  nf_node_new_ext : NodeFn ["child"]
    (fun s Nd =>
      KeyIn s Nd (locN s "nib") (locN s "nlen"))
    (ofString "node_new_ext")
  rt_node_new_ext : Returns ArenaReady (fun s post p => FreshBlock s post p 56)
    (ofString "node_new_ext")
  nf_node_new_leaf : NodeFn []
    (fun s Nd =>
      KeyIn s Nd (locN s "nib") (locN s "nlen"))
    (ofString "node_new_leaf")

structure MptDeleteCallees : Prop where
  fb__collapse_branch : TerminatingFunBoundedOn GuestInv (ofString "_collapse_branch") K.«_collapse_branch»
  fb__delete_ext_finish : TerminatingFunBoundedOn GuestInv (ofString "_delete_ext_finish") K.«_delete_ext_finish»
  fb_common_prefix_length : TerminatingFunBoundedOn GuestInv (ofString "common_prefix_length") K.«common_prefix_length»
  fb_memeq : TerminatingFunBoundedOn GuestInv (ofString "memeq") K.«memeq»
  fb_mpt_fail : TerminatingFunBoundedOn GuestInv (ofString "mpt_fail") K.«mpt_fail»
  fb_node_invalidate : TerminatingFunBoundedOn GuestInv (ofString "node_invalidate") K.«node_invalidate»
  fb_scratch_alloc : TerminatingFunBoundedOn GuestInv (ofString "scratch_alloc") K.«scratch_alloc»
  nf__collapse_branch : NodeFn ["node"]
    (fun s Nd =>
      NodeKind s Nd "node" 3)
    (ofString "_collapse_branch")
  nf__delete_ext_finish : NodeFn ["node", "nc"]
    (fun s Nd =>
      NodeKind s Nd "node" 2 ∧ KeyIn s Nd (locN s "seg") (locN s "sl"))
    (ofString "_delete_ext_finish")
  ro_common_prefix_length : ReadOnlyFn (ofString "common_prefix_length")
  rv_common_prefix_length : RetLe (fun s => min (locN s "al") (locN s "bl")) (ofString "common_prefix_length")
  ro_memeq : ReadOnlyFn (ofString "memeq")
  ro_mpt_fail : ReadOnlyFn (ofString "mpt_fail")
  nf_node_invalidate : NodeFn ["nd"]
    (fun _ _ => True)
    (ofString "node_invalidate")
  iz_node_invalidate : InvalidatesCache (ofString "node_invalidate")
  ww_scratch_alloc : WritesWithin (fun s => [])
    ["scratch_ptr"] (ofString "scratch_alloc")
  rt_scratch_alloc : Returns ArenaReady (fun s post p => FreshScratch s post p (locN s "n") ∧
      globN post "scratch_ptr" = p)
    (ofString "scratch_alloc")

def mptDecBody : ProgHOL 64 → ProgHOL 64
  | .dec _ _ _ p => p
  | _ => .skip
def mptLeft : ProgHOL 64 → ProgHOL 64
  | .seq a _ => a
  | _ => .skip
def mptRight : ProgHOL 64 → ProgHOL 64
  | .seq _ b => b
  | _ => .skip
def mptWhileBody : ProgHOL 64 → ProgHOL 64
  | .while _ b => b
  | _ => .skip
def mptGo : ExpHOL 64 := .cmp .notEqual (.var .local (ofString "go")) (.const 0)
def mptTop : ExpHOL 64 := .cmp .notEqual (.var .local (ofString "top")) (.const 0)
def mptInit (a b : String) (tail : ProgHOL 64) : ProgHOL 64 :=
  .dec (ofString a) .one (.const 0)
    (.dec (ofString b) .one (.const 0) (.dec (ofString "go") .one (.const 1) tail))
def mptReturn (name : String) : ProgHOL 64 := .return (.var .local (ofString name))

def mptInsertCode : ProgHOL 64 := (sourceFunctionEntry Guest.Software.guestFn__mpt_insert_node).2.2.1
def mptDeleteCode : ProgHOL 64 := (sourceFunctionEntry Guest.Software.guestFn__mpt_delete_node_body).2.2.1
def mptInsertTail := mptDecBody (mptDecBody (mptDecBody mptInsertCode))
def mptDeleteTail := mptDecBody (mptDecBody (mptDecBody mptDeleteCode))
def mptInsertBody := mptWhileBody (mptLeft mptInsertTail)
def mptDeleteBody := mptWhileBody (mptLeft mptDeleteTail)
def mptUnwindBody := mptWhileBody (mptLeft (mptRight mptDeleteTail))

theorem mptInsert_lookup : originalRuntimeCode.lookup (ofString "_mpt_insert_node") =
    some ((sourceFunctionEntry Guest.Software.guestFn__mpt_insert_node).2) := by
  exact originalRuntimeCode_lookup_of_guestAst_getElem 275 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn__mpt_insert_node) rfl

theorem mptInsert_ast : mptInsertCode = mptInit "result" "slot"
    (.seq (.while mptGo mptInsertBody) (mptReturn "result")) := rfl
theorem mptDelete_ast : mptDeleteCode = mptInit "top" "res"
    (.seq (.while mptGo mptDeleteBody)
      (.seq (.while mptTop mptUnwindBody) (mptReturn "res"))) := rfl

def mptCharge (f : MlS) : Nat :=
  if f = ofString "_collapse_branch" then K.«_collapse_branch» else
  if f = ofString "_delete_ext_finish" then K.«_delete_ext_finish» else
  if f = ofString "_insert_into_leaf" then K.«_insert_into_leaf» else
  if f = ofString "_split_extension" then K.«_split_extension» else
  if f = ofString "common_prefix_length" then K.«common_prefix_length» else
  if f = ofString "memeq" then K.«memeq» else
  if f = ofString "mpt_fail" then K.«mpt_fail» else
  if f = ofString "node_invalidate" then K.«node_invalidate» else
  if f = ofString "node_new_ext" then K.«node_new_ext» else
  if f = ofString "node_new_leaf" then K.«node_new_leaf» else
  if f = ofString "scratch_alloc" then K.«scratch_alloc» else
  0

def mptCost : ProgHOL 64 → Nat
  | .seq a b => mptCost a + mptCost b
  | .ite _ a b => max (mptCost a) (mptCost b)
  | .dec _ _ _ b => mptCost b
  | .call _ f _ => mptCharge f + 1
  | _ => 0
def mptInsertCost := Nat.max ((K.«node_new_leaf» + 1)) (Nat.max ((K.«mpt_fail» + 1)) (0) + (K.«node_invalidate» + 1) + Nat.max ((K.«_insert_into_leaf» + 1)) (Nat.max ((K.«common_prefix_length» + 1) + Nat.max (0) ((K.«_split_extension» + 1) + Nat.max ((K.«node_new_ext» + 1)) (0))) (0)))
def mptDeleteCost := Nat.max (0) (Nat.max ((K.«mpt_fail» + 1)) (0) + (K.«node_invalidate» + 1) + Nat.max (Nat.max ((K.«memeq» + 1)) (0)) (Nat.max ((K.«common_prefix_length» + 1) + Nat.max (0) ((K.«scratch_alloc» + 1))) (Nat.max (Nat.max (0) ((K.«_collapse_branch» + 1))) ((K.«scratch_alloc» + 1)))))
def mptUnwindCost := Nat.max ((K.«_delete_ext_finish» + 1)) ((K.«_collapse_branch» + 1))
def mptInsertBudget := (2 ^ 130 + 1) * (mptInsertCost + 1)
def mptDeleteBudget := (2 ^ 130 + 1) * (mptDeleteCost + 1)
def mptUnwindBudget := (2 ^ 64 + 1) * (mptUnwindCost + 1)

theorem mptInsert_budget : mptInsertBudget = K._mpt_insert_node := rfl

theorem mptDelete_budget : mptDeleteBudget + mptUnwindBudget = K._mpt_delete_node_body := rfl

/-- A parent slot contains precisely the current node. This makes an unchanged
descent pointer store idempotent; arbitrary writable pointers are insufficient. -/
def MptSlotOK {F : Type} (s : PanSemStateFiniteExact 64 F) (Nd : List Nat) : Prop :=
  locN s "slot" = 0 ∨ ∃ p ∈ Nd,
    ((memW s p = 2 ∧ locN s "slot" = p + 48) ∨
      (memW s p = 3 ∧ ∃ i, i < 16 ∧ locN s "slot" = p + 32 + 8 * i)) ∧
    memW s (locN s "slot") = locN s "node"

def MptInsertHead : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ (locN s "go" ≠ 0 →
    locN s "level" ≤ locN s "klen" ∧ ∃ Nd, NodeHeap s Nd ∧
      RootIn Nd (locN s "node") ∧
      KeyIn s Nd (locN s "key" + locN s "level") (locN s "klen" - locN s "level") ∧
      MptSlotOK s Nd)
def MptInsertActive : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => MptInsertHead s ∧ locN s "go" ≠ 0

/-- Saved 40-byte deletion frames, in increasing address order from the top. -/
def MptFrameOK {F : Type} (s : PanSemStateFiniteExact 64 F) (Nd : List Nat) (p : Nat) : Prop :=
  Inside (p, 40) (globN s "scratch_ptr") scratchEnd ∧ WordsOK s (p, 40) ∧
  let n := memW s (p + 8)
  n ∈ Nd ∧
    ((memW s (p + 16) = 2 ∧ memW s n = 2 ∧
      KeyIn s Nd (memW s (p + 24)) (memW s (p + 32))) ∨
     (memW s (p + 16) = 3 ∧ memW s n = 3 ∧ memW s (p + 32) < 16))

def MptStack {F : Type} (s : PanSemStateFiniteExact 64 F) (Nd : List Nat) : Nat → List Nat → Prop
  | p, [] => p = 0
  | p, q :: qs => p = q ∧ p ≠ 0 ∧ MptFrameOK s Nd p ∧
      (∀ r ∈ qs, p + 40 ≤ r) ∧ MptStack s Nd (memW s p) qs

def MptDeleteHead : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ ∃ Nd fs, NodeHeap s Nd ∧ MptStack s Nd (locN s "top") fs ∧
    RootIn Nd (locN s "res") ∧ (locN s "go" ≠ 0 →
      locN s "level" ≤ locN s "klen" ∧ RootIn Nd (locN s "node") ∧
      KeyIn s Nd (locN s "key" + locN s "level") (locN s "klen" - locN s "level"))
def MptDeleteActive : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => MptDeleteHead s ∧ locN s "go" ≠ 0
def MptUnwindHead : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ ∃ Nd fs, NodeHeap s Nd ∧
    MptStack s Nd (locN s "top") fs ∧ RootIn Nd (locN s "res")

/-- Null roots share shard 0 with hashed nodes. -/
def mptKind {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  if locN s "node" = 0 then 0 else memW s (locN s "node")

theorem mptKind_le {F : Type} {s : PanSemStateFiniteExact 64 F} (h : MptReady s) :
    mptKind s ≤ 3 := by
  obtain ⟨_, _, Nd, hn, hr, _⟩ := h
  unfold mptKind
  split
  · omega
  · rename_i hz
    have hm : locN s "node" ∈ Nd := hr.resolve_left hz
    exact (hn.1 _ hm).1

theorem mptInsert_kind {F : Type} {s : PanSemStateFiniteExact 64 F} (h : MptInsertActive s) :
    mptKind s ≤ 3 := by
  obtain ⟨hl, Nd, hn, hr, hk, _⟩ := h.1.2 h.2
  exact mptKind_le ⟨h.1.1, hl, Nd, hn, hr, hk⟩
theorem mptDelete_kind {F : Type} {s : PanSemStateFiniteExact 64 F} (h : MptDeleteActive s) :
    mptKind s ≤ 3 := by
  obtain ⟨Nd, fs, hn, _, _, ha⟩ := h.1.2
  obtain ⟨hl, hr, hk⟩ := ha h.2
  exact mptKind_le ⟨h.1.1, hl, Nd, hn, hr, hk⟩

/-- The only non-progressing insertion transition is a zero-length extension.
Its memory effect is exactly cache clearing: the parent pointer store is redundant.
The counting shard must handle multi-node cycles, not merely self-loops. -/
def MptInsertEffect {F : Type} (s t : PanSemStateFiniteExact 64 F) : Prop :=
  locN t "go" = 0 ∨
    locN t "key" = locN s "key" ∧ locN t "klen" = locN s "klen" ∧
    locN t "vptr" = locN s "vptr" ∧ locN t "vlen" = locN s "vlen" ∧
    (locN s "level" < locN t "level" ∨
      (locN s "node" ≠ 0 ∧ memW s (locN s "node") = 2 ∧
       memW s (locN s "node" + 40) = 0 ∧
       locN t "level" = locN s "level" ∧
       locN t "node" = memW s (locN s "node" + 48) ∧
       locN t "slot" = locN s "node" + 48 ∧
       locN t "result" = (if locN s "slot" = 0 then locN s "node" else locN s "result") ∧
       t = { clearCache s (locN s "node") with locals := t.locals, clock := t.clock } ∧
       ∀ x : MlS, x ∉ (["go", "node", "slot", "level", "result"].map ofString) →
         t.locals.lookup x = s.locals.lookup x))

/-- Every continuing deletion descent allocates a fresh 40-byte scratch frame. -/
def MptDeleteEffect {F : Type} (s t : PanSemStateFiniteExact 64 F) : Prop :=
  locN t "go" = 0 ∨ globN t "scratch_ptr" + 40 ≤ globN s "scratch_ptr"

def MptFlow {F : Type} (s : PanSemStateFiniteExact 64 F) (body : ProgHOL 64) : Prop :=
  (evaluateHOLFiniteState s body).1 = none ∨ (evaluateHOLFiniteState s body).1 = some .continue

def MptStepAt (P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (E : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Prop)
    (body : ProgHOL 64) (b k : Nat) : Prop :=
  ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → P s →
    mptKind s = k → TerminatingRunBounded s body b ∧
      (MptFlow s body → Q (evaluateHOLFiniteState s body).2 ∧ E s (evaluateHOLFiniteState s body).2)

def MptSteps (P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (E : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Prop)
    (body : ProgHOL 64) (b : Nat) : Prop :=
  ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → P s →
    TerminatingRunBounded s body b ∧
      (MptFlow s body → Q (evaluateHOLFiniteState s body).2 ∧ E s (evaluateHOLFiniteState s body).2)

theorem mpt_cases {P Q E body b}
    (hk : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → mptKind s ≤ 3)
    (h0 : MptStepAt P Q E body b 0) (h1 : MptStepAt P Q E body b 1)
    (h2 : MptStepAt P Q E body b 2) (h3 : MptStepAt P Q E body b 3) :
    MptSteps P Q E body b := by
  intro F s hc hp
  have h := hk s hp
  have cases : mptKind s = 0 ∨ mptKind s = 1 ∨ mptKind s = 2 ∨ mptKind s = 3 := by omega
  rcases cases with h | h | h | h
  · exact h0 s hc hp h
  · exact h1 s hc hp h
  · exact h2 s hc hp h
  · exact h3 s hc hp h

end InitECandidate.Solver.Wave8GuestInv.GuardedBody
